# tomasulo_core.py
# -------------------------------------------------------------
# Núcleo do simulador didático do Algoritmo de Tomasulo
# (sem interface gráfica)
# -------------------------------------------------------------

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple, Any
import copy
import re

# ==========================
# Parâmetros padrão
# ==========================
DEFAULT_LATENCIES = {
    "ADD": 2,
    "SUB": 2,
    "MUL": 8,
    "DIV": 16,
    "LD": 3,
    "ST": 3,
    "BEQ": 1,
    "BNE": 1,
}

DEFAULT_SIZES = {
    "RS_ADD": 4,
    "RS_MUL": 3,
    "RS_LS": 4,
    "RS_BR": 2,
    "ROB": 16,
}

NUM_REGS = 16  # R0..R15
MEM_SIZE = 256  # memória pequena para LD/ST

# ==========================
# Classes de dados
# ==========================
@dataclass
class Instruction:
    op: str
    rd: Optional[int] = None
    rs1: Optional[int] = None
    rs2: Optional[int] = None
    imm: Optional[int] = None
    label: Optional[str] = None
    pc: int = 0  # índice na lista de instruções

    def __str__(self):
        if self.op in ("ADD", "SUB", "MUL", "DIV"):
            return f"{self.op} R{self.rd}, R{self.rs1}, R{self.rs2}"
        if self.op == "LD":
            return f"LD R{self.rd}, {self.imm}(R{self.rs1})"
        if self.op == "ST":
            return f"ST R{self.rs1}, {self.imm}(R{self.rs2})"
        if self.op in ("BEQ", "BNE"):
            tgt = self.label if self.label else self.imm
            return f"{self.op} R{self.rs1}, R{self.rs2}, {tgt}"
        if self.op in ("NOP", "HALT"):
            return self.op
        return f"{self.op} ?"


@dataclass
class ROBEntry:
    idx: int
    instr: Instruction
    dest_arch: Optional[int]
    ready: bool = False
    value: Optional[int] = None
    state: str = "ISSUE"  # ISSUE/EXEC/WB/COMMIT
    mispredict: bool = False
    rename_snapshot: Optional[Dict[int, Optional[int]]] = None


@dataclass
class RSEntry:
    busy: bool = False
    op: Optional[str] = None
    Vj: Optional[int] = None
    Vk: Optional[int] = None
    Qj: Optional[int] = None  # tag ROB
    Qk: Optional[int] = None
    A: Optional[int] = None   # deslocamento/endereço
    dest_tag: Optional[int] = None  # tag ROB destino
    remaining: int = 0
    instr_pc: int = -1


class BranchPredictor2Bit:
    """Preditor bimodal 2-bits simples: tabela indexada por PC mod N."""

    def __init__(self, size: int = 64):
        self.size = size
        self.counters = [1] * size  # 0..3
        self.targets: List[Optional[int]] = [None] * size

    def _idx(self, pc: int) -> int:
        return pc % self.size

    def predict(self, pc: int) -> Tuple[bool, Optional[int]]:
        i = self._idx(pc)
        take = self.counters[i] >= 2
        return take, self.targets[i]

    def update(self, pc: int, taken: bool, target: Optional[int]):
        i = self._idx(pc)
        if taken:
            self.counters[i] = min(3, self.counters[i] + 1)
        else:
            self.counters[i] = max(0, self.counters[i] - 1)
        if target is not None:
            self.targets[i] = target


# ==========================
# Núcleo do simulador
# ==========================
class TomasuloSim:
    def __init__(self, program: List[Instruction], latencies: Dict[str, int], sizes: Dict[str, int]):
        self.program = program
        self.lat = latencies
        self.sizes = sizes

        # Estado arquitetural
        self.arch_regs = [0] * NUM_REGS
        self.memory = [0] * MEM_SIZE

        # Mapa de renomeação (arch reg -> tag ROB ou None)
        self.rename: Dict[int, Optional[int]] = {i: None for i in range(NUM_REGS)}

        # ROB circular
        self.rob: List[Optional[ROBEntry]] = [None] * self.sizes["ROB"]
        self.rob_head = 0
        self.rob_tail = 0
        self.rob_count = 0

        # Estações de reserva
        self.RS_ADD: List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_ADD"])]
        self.RS_MUL: List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_MUL"])]
        self.RS_LS: List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_LS"])]
        self.RS_BR: List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_BR"])]

        # CDB (uma escrita por ciclo)
        self.cdb: Optional[Tuple[int, Any]] = None  # (tag, value)

        # Preditor de desvio
        self.pred = BranchPredictor2Bit(size=64)

        # Controle
        self.pc = 0
        self.halted = False
        self.cycle = 0

        # Métricas
        self.committed = 0
        self.issued = 0
        self.exec_busy_cycles = 0
        self.bubble_cycles = 0

        # Log do ciclo
        self.events: List[str] = []

    # ----------- Utilitários do ROB -----------
    def rob_is_full(self) -> bool:
        return self.rob_count == len(self.rob)

    def rob_alloc(self, instr: Instruction, dest_arch: Optional[int]) -> int:
        assert not self.rob_is_full()
        idx = self.rob_tail
        entry = ROBEntry(idx=idx, instr=instr, dest_arch=dest_arch)
        self.rob[idx] = entry
        self.rob_tail = (self.rob_tail + 1) % len(self.rob)
        self.rob_count += 1
        return idx

    def rob_peek_head(self) -> Optional[ROBEntry]:
        if self.rob_count == 0:
            return None
        return self.rob[self.rob_head]

    def rob_pop(self) -> Optional[ROBEntry]:
        if self.rob_count == 0:
            return None
        e = self.rob[self.rob_head]
        self.rob[self.rob_head] = None
        self.rob_head = (self.rob_head + 1) % len(self.rob)
        self.rob_count -= 1
        return e

    # ----------- Busca de RS livre -----------
    def find_rs(self, kind: str) -> Optional[RSEntry]:
        if kind in ("NOP", "HALT"):
            table = self.RS_BR
        else:
            table = {
                "ADD": self.RS_ADD,
                "SUB": self.RS_ADD,
                "MUL": self.RS_MUL,
                "DIV": self.RS_MUL,
                "LD": self.RS_LS,
                "ST": self.RS_LS,
                "BEQ": self.RS_BR,
                "BNE": self.RS_BR,
            }[kind]
        for rs in table:
            if not rs.busy:
                return rs
        return None

    # ----------- Leitura de operandos -----------
    def get_src(self, reg: int) -> Tuple[Optional[int], Optional[int]]:
        tag = self.rename.get(reg)
        if tag is None:
            return self.arch_regs[reg], None
        return None, tag

    # ----------- Issue / Dispatch -----------
    def issue(self) -> bool:
        if self.halted or self.pc >= len(self.program):
            return False

        instr = self.program[self.pc]
        dest_arch = None
        if instr.op in ("ADD", "SUB", "MUL", "DIV", "LD"):
            dest_arch = instr.rd

        rs = self.find_rs(instr.op)
        if rs is None or self.rob_is_full():
            return False  # stall estrutural

        # Aloca ROB
        tag = self.rob_alloc(instr, dest_arch)

        # Atualiza rename map
        if dest_arch is not None:
            self.rename[dest_arch] = tag

        # Preenche RS
        rs.busy = True
        rs.op = instr.op
        rs.dest_tag = tag
        rs.instr_pc = instr.pc
        rs.remaining = self.lat[instr.op]

        if instr.op in ("ADD", "SUB", "MUL", "DIV"):
            Vj, Qj = self.get_src(instr.rs1)
            Vk, Qk = self.get_src(instr.rs2)
            rs.Vj, rs.Qj = Vj, Qj
            rs.Vk, rs.Qk = Vk, Qk
        elif instr.op == "LD":
            Vj, Qj = self.get_src(instr.rs1)
            rs.Vj, rs.Qj = Vj, Qj
            rs.A = instr.imm or 0
        elif instr.op == "ST":
            Vval, Qval = self.get_src(instr.rs1)
            Vbase, Qbase = self.get_src(instr.rs2)
            rs.Vj, rs.Qj = Vval, Qval   # valor
            rs.Vk, rs.Qk = Vbase, Qbase # base
            rs.A = instr.imm or 0
        elif instr.op in ("BEQ", "BNE"):
            Vj, Qj = self.get_src(instr.rs1)
            Vk, Qk = self.get_src(instr.rs2)
            rs.Vj, rs.Qj = Vj, Qj
            rs.Vk, rs.Qk = Vk, Qk
            # snapshot do rename para possível flush
            self.rob[tag].rename_snapshot = copy.deepcopy(self.rename)
        elif instr.op in ("NOP", "HALT"):
            pass

        # Predição de desvio
        advance_pc = True
        if instr.op in ("BEQ", "BNE"):
            taken_pred, target_pred = self.pred.predict(instr.pc)
            if taken_pred and target_pred is not None:
                self.pc = target_pred
                advance_pc = False
        if advance_pc:
            self.pc += 1

        self.issued += 1
        self.events.append(f"Issue: {instr} -> ROB{tag}")
        return True

    # ----------- Execução -----------
    def can_start(self, rs: RSEntry) -> bool:
        return rs.busy and rs.remaining > 0 and rs.Qj is None and rs.Qk is None

    def execute(self) -> bool:
        started_any = False

        any_active = any(
            rs.busy and rs.remaining > 0
            for rs in (self.RS_ADD + self.RS_MUL + self.RS_LS + self.RS_BR)
        )
        if any_active:
            self.exec_busy_cycles += 1

        for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
            for rs in table:
                if self.can_start(rs):
                    rs.remaining -= 1
                    started_any = True

                    if rs.remaining == 0 and self.cdb is None:
                        val: Any = None
                        op = rs.op
                        if op == "ADD":
                            val = rs.Vj + rs.Vk
                        elif op == "SUB":
                            val = rs.Vj - rs.Vk
                        elif op == "MUL":
                            val = rs.Vj * rs.Vk
                        elif op == "DIV":
                            val = rs.Vj // rs.Vk if rs.Vk != 0 else 0
                        elif op == "LD":
                            addr = (rs.Vj + (rs.A or 0)) % MEM_SIZE
                            val = self.memory[addr]
                        elif op == "ST":
                            addr = (rs.Vk + (rs.A or 0)) % MEM_SIZE
                            val = ("STORE", addr, rs.Vj)
                        elif op in ("BEQ", "BNE"):
                            taken = (rs.Vj == rs.Vk) if op == "BEQ" else (rs.Vj != rs.Vk)
                            val = ("BR", taken)

                        if val is not None:
                            tag = rs.dest_tag if rs.dest_tag is not None else -1
                            self.cdb = (tag, val)
                            self.events.append(f"Exec done: {op} -> CDB({tag})")

        return started_any

    # ----------- Writeback -----------
    def writeback(self):
        if self.cdb is None:
            return
        tag, value = self.cdb

        # Atualiza RS
        for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
            for rs in table:
                if rs.busy:
                    if rs.Qj == tag:
                        rs.Vj = value
                        rs.Qj = None
                    if rs.Qk == tag:
                        rs.Vk = value
                        rs.Qk = None

        # Atualiza ROB
        if tag >= 0:
            entry = self.rob[tag]
            if entry:
                entry.value = value
                entry.ready = True
                entry.state = "WB"

        self.cdb = None

    # ----------- Commit -----------
    def commit(self) -> int:
        committed_this_cycle = 0
        head = self.rob_peek_head()
        if head and head.ready:
            entry = self.rob_pop()
            instr = entry.instr

            if instr.op in ("ADD", "SUB", "MUL", "DIV", "LD"):
                if entry.dest_arch is not None and self.rename.get(entry.dest_arch) == entry.idx:
                    if not (isinstance(entry.value, tuple) and entry.value[0] == "STORE"):
                        self.arch_regs[entry.dest_arch] = int(entry.value)
                        self.rename[entry.dest_arch] = None
            elif instr.op == "ST":
                if isinstance(entry.value, tuple) and entry.value[0] == "STORE":
                    _, addr, val = entry.value
                    self.memory[addr] = int(val)
            elif instr.op in ("BEQ", "BNE"):
                if isinstance(entry.value, tuple) and entry.value[0] == "BR":
                    taken_real = entry.value[1]
                    taken_pred, target_pred = self.pred.predict(instr.pc)
                    target_real = instr.imm

                    self.pred.update(instr.pc, taken_real, target_real)

                    pred_pc = target_pred if taken_pred and target_pred is not None else instr.pc + 1
                    real_pc = target_real if taken_real else instr.pc + 1
                    if pred_pc != real_pc:
                        entry.mispredict = True
                        self.flush_after(entry.idx)
                        self.pc = real_pc
            elif instr.op == "HALT":
                self.halted = True

            # Limpa RS associada
            for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
                for rs in table:
                    if rs.busy and (rs.dest_tag == entry.idx or rs.instr_pc == instr.pc):
                        rs.__dict__.update(RSEntry().__dict__)

            committed_this_cycle += 1
            self.committed += committed_this_cycle
            self.events.append(f"Commit: ROB{entry.idx} :: {instr}")

        return committed_this_cycle

    # ----------- Flush em caso de erro de predição -----------
    def flush_after(self, rob_idx: int):
        i = (rob_idx + 1) % len(self.rob)
        removed = []
        while i != self.rob_tail:
            if self.rob[i] is not None:
                removed.append(self.rob[i].idx)
            self.rob[i] = None
            i = (i + 1) % len(self.rob)
        self.rob_tail = (rob_idx + 1) % len(self.rob)

        cnt = 0
        j = self.rob_head
        while True:
            if self.rob[j] is not None:
                cnt += 1
            if j == rob_idx:
                break
            j = (j + 1) % len(self.rob)
        self.rob_count = cnt

        # Limpa RS com dest_tag > rob_idx (heurística simples)
        for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
            for rs in table:
                if rs.busy and rs.dest_tag is not None and rs.dest_tag != -1 and rs.dest_tag > rob_idx:
                    rs.__dict__.update(RSEntry().__dict__)

        snap = self.rob[rob_idx].rename_snapshot if self.rob[rob_idx] else None
        if snap is not None:
            self.rename = snap

        self.events.append(f"Flush: após ROB{rob_idx} | removidos {removed}")

    # ----------- Um ciclo completo -----------
    def step_cycle(self):
        if self.halted:
            return
        self.cycle += 1
        self.events = []

        issued_now = self.issue()
        self.execute()
        self.writeback()
        self.commit()

        if (not issued_now) and (self.pc < len(self.program)) and (not self.halted):
            self.bubble_cycles += 1

    # ----------- Métricas -----------
    def metrics(self) -> Dict[str, Any]:
        ipc = self.committed / self.cycle if self.cycle > 0 else 0.0
        return {
            "Ciclos": self.cycle,
            "Commits": self.committed,
            "IPC": round(ipc, 3),
            "Bolhas (stall de emissão)": self.bubble_cycles,
            "RS_ADD ocupadas": sum(1 for r in self.RS_ADD if r.busy),
            "RS_MUL ocupadas": sum(1 for r in self.RS_MUL if r.busy),
            "RS_LS ocupadas": sum(1 for r in self.RS_LS if r.busy),
            "RS_BR ocupadas": sum(1 for r in self.RS_BR if r.busy),
            "ROB ocupadas": self.rob_count,
        }


# ==========================
# Montagem simples
# ==========================
LABEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):$")


def parse_reg(tok: str) -> int:
    tok = tok.strip().upper()
    assert tok.startswith("R"), f"Registrador inválido: {tok}"
    return int(tok[1:])


def assemble(text: str) -> List[Instruction]:
    lines = [
        l.strip()
        for l in text.splitlines()
        if l.strip() and not l.strip().startswith("#") and not l.strip().startswith(";")
    ]

    labels: Dict[str, int] = {}
    pc = 0
    tmp: List[str] = []

    # 1ª passagem: labels
    for l in lines:
        m = LABEL_RE.match(l)
        if m:
            labels[m.group(1)] = pc
        else:
            tmp.append(l)
            pc += 1

    # 2ª passagem: instruções
    out: List[Instruction] = []
    pc = 0
    for l in tmp:
        parts = re.split(r"[\s,()]+", l)
        parts = [p for p in parts if p]
        op = parts[0].upper()

        if op in ("ADD", "SUB", "MUL", "DIV"):
            rd = parse_reg(parts[1])
            rs1 = parse_reg(parts[2])
            rs2 = parse_reg(parts[3])
            instr = Instruction(op=op, rd=rd, rs1=rs1, rs2=rs2, pc=pc)
        elif op == "LD":
            rd = parse_reg(parts[1])
            imm = int(parts[2])
            rs1 = parse_reg(parts[3])
            instr = Instruction(op=op, rd=rd, rs1=rs1, imm=imm, pc=pc)
        elif op == "ST":
            rs_val = parse_reg(parts[1])
            imm = int(parts[2])
            rs_base = parse_reg(parts[3])
            instr = Instruction(op=op, rs1=rs_val, rs2=rs_base, imm=imm, pc=pc)
        elif op in ("BEQ", "BNE"):
            rs1 = parse_reg(parts[1])
            rs2 = parse_reg(parts[2])
            target = parts[3]
            if target.isdigit():
                tgt_pc = int(target)
            else:
                tgt_pc = labels.get(target)
                if tgt_pc is None:
                    raise ValueError(f"Label desconhecida: {target}")
            instr = Instruction(op=op, rs1=rs1, rs2=rs2, imm=tgt_pc, label=target, pc=pc)
        elif op in ("NOP", "HALT"):
            instr = Instruction(op=op, pc=pc)
        else:
            raise ValueError(f"Opcode inválido: {op}")

        out.append(instr)
        pc += 1

    return out


# ==========================
# Programa exemplo
# ==========================
DEFAULT_PROGRAM = """
# Exemplo didático: soma, load/store e desvio
# Inicializa: R1=10, R2=20, R3=0, mem[0]=5

start:
    ADD R3, R1, R2     # R3 = 10 + 20
    LD R4, 0(R0)       # R4 = mem[0] (=5)
    SUB R5, R4, R1     # R5 = 5 - 10
    BEQ R5, R3, taken  # provavelmente não toma
    MUL R6, R1, R4     # R6 = 10 * 5
    BNE R6, R2, taken  # provável tomar
    NOP
    NOP
    HALT

taken:
    ADD R7, R6, R3
    HALT
"""

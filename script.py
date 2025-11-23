# tomasulo_app.py
# -------------------------------------------------------------
# Simulador didático do Algoritmo de Tomasulo com ROB e especulação
# Implementado em Python + Streamlit (interface gráfica)
# -------------------------------------------------------------
# Principais recursos:
# - Instruções: ADD, SUB, MUL, DIV, LD, ST, BEQ, BNE, NOP, HALT
# - Estações de reserva (Add/Mult/Load/Store/Branch), CDB, renomeação de registradores
# - Buffer de Reordenamento (ROB) com commit em ordem
# - Especulação de desvio com preditor bimodal de 2 bits (tabela simples)
# - Execução passo a passo, rodar N ciclos e rodar até término
# - Métricas: ciclos, IPC, commits, bolhas (definição didática), ocupações
# - Visualizações: ROB, Estações, Registradores, Mapa de Renomeação, Memória, Log do ciclo
# -------------------------------------------------------------

from __future__ import annotations
import streamlit as st
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Any
import copy

# ==========================
# Configurações padrão
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

NUM_REGS = 16  # R0..R15 para fins didáticos
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
    pc: int = 0  # endereço da instrução (índice de lista)

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
    dest_arch: Optional[int]  # registrador arquitetural destino (ou None)
    ready: bool = False
    value: Optional[int] = None
    state: str = "ISSUE"  # ISSUE/EXEC/WB/COMMIT
    mispredict: bool = False
    rename_snapshot: Optional[Dict[int, Optional[int]]] = None  # snapshot do RenameMap (ROB tag por reg)

@dataclass
class RSEntry:
    busy: bool = False
    op: Optional[str] = None
    Vj: Optional[int] = None
    Vk: Optional[int] = None
    Qj: Optional[int] = None  # tag ROB
    Qk: Optional[int] = None
    A: Optional[int] = None   # deslocamento/imediato/endereço efetivo
    dest_tag: Optional[int] = None  # tag ROB destino (para writeback)
    remaining: int = 0
    instr_pc: int = -1

class BranchPredictor2Bit:
    """Preditor bimodal 2-bits simples: tabela indexada por PC mod N."""
    def __init__(self, size: int = 64):
        self.size = size
        self.counters = [1] * size  # 0: fortemente NT, 1: fracamente NT, 2: fracamente T, 3: fortemente T
        self.targets = [None] * size

    def _idx(self, pc: int) -> int:
        return pc % self.size

    def predict(self, pc: int) -> Tuple[bool, Optional[int]]:
        i = self._idx(pc)
        take = self.counters[i] >= 2
        return take, self.targets[i]

    def update(self, pc: int, taken: bool, target: Optional[int]):
        i = self._idx(pc)
        # Atualiza saturando
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
    def __init__(self, program: List[Instruction], latencies: Dict[str,int], sizes: Dict[str,int]):
        self.program = program
        self.lat = latencies
        self.sizes = sizes

        # Estado arquitetural
        self.arch_regs = [0]*NUM_REGS
        self.memory = [0]*MEM_SIZE

        # Mapa de renomeação (arch reg -> ROB tag ou None se valor pronto em arch_regs)
        self.rename: Dict[int, Optional[int]] = {i: None for i in range(NUM_REGS)}

        # ROB circular
        self.rob: List[Optional[ROBEntry]] = [None]*self.sizes["ROB"]
        self.rob_head = 0
        self.rob_tail = 0
        self.rob_count = 0

        # Estações de reserva
        self.RS_ADD: List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_ADD"])]
        self.RS_MUL: List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_MUL"])]
        self.RS_LS:  List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_LS"])]
        self.RS_BR:  List[RSEntry] = [RSEntry() for _ in range(self.sizes["RS_BR"])]

        # CDB (uma escrita por ciclo para simplicidade)
        self.cdb: Optional[Tuple[int,int]] = None  # (tag, value)

        # Preditor de desvio
        self.pred = BranchPredictor2Bit(size=64)

        # PC e controle
        self.pc = 0
        self.halted = False
        self.cycle = 0

        # Métricas
        self.committed = 0
        self.issued = 0
        self.exec_busy_cycles = 0
        self.bubble_cycles = 0  # definido como: ciclo com instruções por emitir, mas nenhuma emissão ocorreu

        # Log do ciclo
        self.events: List[str] = []

    # ----------- Utilitários ROB -----------
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
                "BNE": self.RS_BR
            }[kind]
        for rs in table:
            if not rs.busy:
                return rs
        return None

    # ----------- Leitura do valor/dep Q -----------
    def get_src(self, reg: int) -> Tuple[Optional[int], Optional[int]]:
        tag = self.rename.get(reg)
        if tag is None:
            return self.arch_regs[reg], None
        return None, tag

    # ----------- Emissão/Despacho -----------
    def issue(self):
        if self.halted or self.pc >= len(self.program):
            return False

        instr = self.program[self.pc]
        # Determinar destino arquitetural, se houver
        dest_arch = None
        if instr.op in ("ADD","SUB","MUL","DIV","LD"):
            dest_arch = instr.rd
        # ST não tem destino; BEQ/BNE também não; NOP/HALT não

        # Verificar capacidade
        rs = self.find_rs(instr.op)
        if rs is None or self.rob_is_full():
            return False  # stall estrutural

        # Alocar ROB
        tag = self.rob_alloc(instr, dest_arch)

        # Atualizar rename map para destino
        if dest_arch is not None:
            self.rename[dest_arch] = tag

        # Preencher RS
        rs.busy = True
        rs.op = instr.op
        rs.dest_tag = tag
        rs.instr_pc = instr.pc
        rs.remaining = self.lat[instr.op]

        if instr.op in ("ADD","SUB","MUL","DIV"):
            Vj,Qj = self.get_src(instr.rs1)
            Vk,Qk = self.get_src(instr.rs2)
            rs.Vj, rs.Qj = Vj, Qj
            rs.Vk, rs.Qk = Vk, Qk
        elif instr.op == "LD":
            Vj,Qj = self.get_src(instr.rs1)
            rs.Vj, rs.Qj = Vj, Qj  # base
            rs.A = instr.imm or 0
        elif instr.op == "ST":
            # valor a armazenar em rs.Vj/Qj, base em rs.Vk/Qk
            Vval,Qval = self.get_src(instr.rs1)
            Vbase,Qbase = self.get_src(instr.rs2)
            rs.Vj, rs.Qj = Vval, Qval
            rs.Vk, rs.Qk = Vbase, Qbase
            rs.A = instr.imm or 0
        elif instr.op in ("BEQ","BNE"):
            Vj,Qj = self.get_src(instr.rs1)
            Vk,Qk = self.get_src(instr.rs2)
            rs.Vj, rs.Qj = Vj, Qj
            rs.Vk, rs.Qk = Vk, Qk
            # snapshot do rename para possível flush
            self.rob[(tag)%len(self.rob)].rename_snapshot = copy.deepcopy(self.rename)
        elif instr.op == "NOP":
            pass
        elif instr.op == "HALT":
            pass

        # Especulação para branch: define PC com base no preditor
        advance_pc = True
        if instr.op in ("BEQ","BNE"):
            taken_pred, target_pred = self.pred.predict(instr.pc)
            if taken_pred and target_pred is not None:
                self.pc = target_pred
                advance_pc = False
            # se sem target conhecido, prediz não tomado (avança sequencialmente)
        if advance_pc:
            self.pc += 1

        self.issued += 1
        self.events.append(f"Issue: {instr} -> ROB{tag}")
        return True

    # ----------- Execução -----------
    def can_start(self, rs: RSEntry) -> bool:
        return rs.busy and rs.remaining > 0 and rs.Qj is None and rs.Qk is None

    def execute(self):
        started_any = False
        # Marcar ciclos ocupados se qualquer RS estiver ativa
        any_active = any(rs.busy and rs.remaining > 0 for rs in (self.RS_ADD+self.RS_MUL+self.RS_LS+self.RS_BR))
        if any_active:
            self.exec_busy_cycles += 1

        for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
            for rs in table:
                if self.can_start(rs):
                    rs.remaining -= 1
                    started_any = True
                    # Se terminar agora, agenda writeback via CDB (uma por ciclo; prioriza primeira encontrada)
                    if rs.remaining == 0 and self.cdb is None:
                        val = None
                        # Calcula resultado
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
                            # ST escreve no commit para simplicidade: passamos o par (addr, value) via value codificado
                            addr = (rs.Vk + (rs.A or 0)) % MEM_SIZE
                            val = ("STORE", addr, rs.Vj)
                        elif op in ("BEQ","BNE"):
                            taken = (rs.Vj == rs.Vk) if op == "BEQ" else (rs.Vj != rs.Vk)
                            # target real é computado do programa (label resolvida na montagem)
                            val = ("BR", taken)
                        if val is not None:
                            self.cdb = (rs.dest_tag if rs.dest_tag is not None else -1, val)
                            self.events.append(f"Exec done: {op} -> CDB({self.cdb[0]})")
                # Nota: apenas uma emissão no CDB por ciclo para simplificar conflito
        return started_any

    # ----------- Writeback (CDB broadcast) -----------
    def writeback(self):
        if self.cdb is None:
            return
        tag, value = self.cdb

        # Atualiza RS pendentes
        for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
            for rs in table:
                if rs.busy:
                    if rs.Qj == tag:
                        rs.Vj = value if not (isinstance(value, tuple) and value[0] == "STORE") else value  # para ST, Vj pode ser tupla STORE
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
    def commit(self):
        committed_this_cycle = 0
        # Um commit por ciclo para simplificação (poderia ser múltiplo)
        head = self.rob_peek_head()
        if head and head.ready:
            entry = self.rob_pop()
            instr = entry.instr
            # Tratamento por tipo
            if instr.op in ("ADD","SUB","MUL","DIV","LD"):
                # Escreve no registrador arquitetural se o rename ainda aponta para este tag
                if entry.dest_arch is not None and self.rename.get(entry.dest_arch) == entry.idx:
                    if isinstance(entry.value, tuple) and entry.value[0] == "STORE":
                        pass  # não deve ocorrer
                    else:
                        self.arch_regs[entry.dest_arch] = int(entry.value)
                        self.rename[entry.dest_arch] = None
            elif instr.op == "ST":
                # entry.value: ("STORE", addr, val)
                if isinstance(entry.value, tuple) and entry.value[0] == "STORE":
                    _, addr, val = entry.value
                    self.memory[addr] = int(val)
            elif instr.op in ("BEQ","BNE"):
                # entry.value: ("BR", taken)
                if isinstance(entry.value, tuple) and entry.value[0] == "BR":
                    taken_real = entry.value[1]
                    # Predição feita no issue
                    taken_pred, target_pred = self.pred.predict(instr.pc)
                    # Target real
                    target_real = instr.imm  # montador coloca PC alvo aqui
                    # Atualiza preditor
                    self.pred.update(instr.pc, taken_real, target_real)

                    # Verifica misspeculation
                    pred_pc = target_pred if taken_pred and target_pred is not None else instr.pc + 1
                    real_pc = target_real if taken_real else instr.pc + 1
                    if pred_pc != real_pc:
                        entry.mispredict = True
                        self.flush_after(entry.idx)
                        self.pc = real_pc
            elif instr.op == "HALT":
                self.halted = True

            # Limpa RS correspondente (a que possui dest_tag == entry.idx ou cujo instr_pc == instr.pc)
            for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
                for rs in table:
                    if rs.busy and (rs.dest_tag == entry.idx or rs.instr_pc == instr.pc):
                        rs.__dict__.update(RSEntry().__dict__)

            committed_this_cycle += 1
            self.events.append(f"Commit: ROB{entry.idx} :: {instr}")

        # bolha didática: havia instruções por emitir/exec, mas nada foi emitido neste ciclo
        # vamos marcar no fim do ciclo (em cycle())
        return committed_this_cycle

    def flush_after(self, rob_idx: int):
        # Invalida entradas do ROB após rob_idx
        i = (rob_idx + 1) % len(self.rob)
        removed = []
        while i != self.rob_tail:
            if self.rob[i] is not None:
                removed.append(self.rob[i].idx)
            self.rob[i] = None
            i = (i + 1) % len(self.rob)
        # Ajusta tail
        self.rob_tail = (rob_idx + 1) % len(self.rob)
        # Reconta
        # (Mantém as entradas válidas de [head..rob_idx])
        cnt = 0
        j = self.rob_head
        while True:
            if self.rob[j] is not None:
                cnt += 1
            if j == rob_idx:
                break
            j = (j + 1) % len(self.rob)
        self.rob_count = cnt

        # Limpa RS com dest_tag maior que rob_idx (heurística)
        for table in [self.RS_ADD, self.RS_MUL, self.RS_LS, self.RS_BR]:
            for rs in table:
                if rs.busy and rs.dest_tag is not None and rs.dest_tag != -1 and rs.dest_tag > rob_idx:
                    rs.__dict__.update(RSEntry().__dict__)

        # Restaura rename map do snapshot do branch
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
        executed = self.execute()
        self.writeback()
        committed_now = self.commit()

        # marca bolha
        if (not issued_now) and (self.pc < len(self.program)) and (not self.halted):
            # há instruções a emitir mas travou
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
import re

LABEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*):$")


def parse_reg(tok: str) -> int:
    tok = tok.strip().upper()
    assert tok.startswith("R"), f"Registrador inválido: {tok}"
    return int(tok[1:])


def assemble(text: str) -> List[Instruction]:
    lines = [l.strip() for l in text.splitlines() if l.strip() and not l.strip().startswith("#") and not l.strip().startswith(";")]
    # 1a passagem: coletar labels
    labels: Dict[str,int] = {}
    pc = 0
    tmp = []
    for l in lines:
        m = LABEL_RE.match(l)
        if m:
            labels[m.group(1)] = pc
        else:
            tmp.append(l)
            pc += 1

    # 2a passagem: gerar instruções
    out: List[Instruction] = []
    pc = 0
    for l in tmp:
        parts = re.split(r"[\s,()]+", l)
        parts = [p for p in parts if p]
        op = parts[0].upper()
        instr = None
        if op in ("ADD","SUB","MUL","DIV"):
            rd = parse_reg(parts[1]); rs1 = parse_reg(parts[2]); rs2 = parse_reg(parts[3])
            instr = Instruction(op=op, rd=rd, rs1=rs1, rs2=rs2, pc=pc)
        elif op == "LD":
            rd = parse_reg(parts[1]); imm = int(parts[2]); rs1 = parse_reg(parts[3])
            instr = Instruction(op=op, rd=rd, rs1=rs1, imm=imm, pc=pc)
        elif op == "ST":
            rs_val = parse_reg(parts[1]); imm = int(parts[2]); rs_base = parse_reg(parts[3])
            instr = Instruction(op=op, rs1=rs_val, rs2=rs_base, imm=imm, pc=pc)
        elif op in ("BEQ","BNE"):
            rs1 = parse_reg(parts[1]); rs2 = parse_reg(parts[2]); target = parts[3]
            if target.isdigit():
                tgt_pc = int(target)
            else:
                tgt_pc = labels.get(target)
                if tgt_pc is None:
                    raise ValueError(f"Label desconhecida: {target}")
            instr = Instruction(op=op, rs1=rs1, rs2=rs2, imm=tgt_pc, label=target, pc=pc)
        elif op == "NOP":
            instr = Instruction(op=op, pc=pc)
        elif op == "HALT":
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
# (Você pode mudar os registradores na GUI)

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

# ==========================
# Interface Streamlit
# ==========================

st.set_page_config(page_title="Simulador de Tomasulo (c/ ROB & Especulação)", layout="wide")

st.title("Simulador de Tomasulo — ROB + Especulação")

with st.sidebar:
    st.header("Configuração")
    col_lat1, col_lat2 = st.columns(2)
    with col_lat1:
        lat_add = st.number_input("Latência ADD/SUB", 1, 20, DEFAULT_LATENCIES["ADD"])
        lat_mul = st.number_input("Latência MUL", 1, 50, DEFAULT_LATENCIES["MUL"])
        lat_div = st.number_input("Latência DIV", 1, 80, DEFAULT_LATENCIES["DIV"])
        lat_ld = st.number_input("Latência LD", 1, 30, DEFAULT_LATENCIES["LD"])
    with col_lat2:
        lat_st = st.number_input("Latência ST", 1, 30, DEFAULT_LATENCIES["ST"])
        lat_br = st.number_input("Latência BEQ/BNE", 1, 10, DEFAULT_LATENCIES["BEQ"])
        rs_add = st.number_input("RS ADD (tam)", 1, 16, DEFAULT_SIZES["RS_ADD"])
        rs_mul = st.number_input("RS MUL (tam)", 1, 16, DEFAULT_SIZES["RS_MUL"])
        rs_ls = st.number_input("RS LD/ST (tam)", 1, 16, DEFAULT_SIZES["RS_LS"])
        rs_br = st.number_input("RS Branch (tam)", 1, 16, DEFAULT_SIZES["RS_BR"])
        rob_sz = st.number_input("ROB (tam)", 4, 64, DEFAULT_SIZES["ROB"])

    st.markdown("---")
    st.subheader("Estado inicial")
    init_regs = st.text_input("Registradores (R0..R15, separados por vírgula)", "0,10,20,0,0,0,0,0,0,0,0,0,0,0,0,0")
    init_mem0 = st.number_input("mem[0]", -999999, 999999, 5)

    st.markdown("---")
    runN = st.number_input("Rodar N ciclos", 1, 1000, 10)

# Código-fonte do programa
prog_text = st.text_area("Programa (ASM didático)", value=DEFAULT_PROGRAM, height=280)

# Estado na sessão
if "sim" not in st.session_state or st.button("(Re)Montar & Resetar", type="primary"):
    try:
        prog = assemble(prog_text)
    except Exception as e:
        st.error(f"Erro na montagem: {e}")
        st.stop()

    lat = {
        "ADD": int(lat_add),
        "SUB": int(lat_add),
        "MUL": int(lat_mul),
        "DIV": int(lat_div),
        "LD": int(lat_ld),
        "ST": int(lat_st),
        "BEQ": int(lat_br),
        "BNE": int(lat_br),
        "NOP": 1,
        "HALT": 1,
    }
    sizes = {
        "RS_ADD": int(rs_add),
        "RS_MUL": int(rs_mul),
        "RS_LS": int(rs_ls),
        "RS_BR": int(rs_br),
        "ROB": int(rob_sz),
    }
    sim = TomasuloSim(prog, lat, sizes)
    # Inicialização conforme GUI
    try:
        vals = [int(x.strip()) for x in init_regs.split(",")]
        if len(vals) != NUM_REGS:
            raise ValueError("Forneça 16 valores (R0..R15)")
        sim.arch_regs = vals
    except Exception as e:
        st.warning(f"Registradores iniciais inválidos: {e}")
    sim.memory[0] = int(init_mem0)
    st.session_state.sim = sim

sim: TomasuloSim = st.session_state.sim

# Controles de execução
c1, c2, c3, c4 = st.columns([1,1,1,2])
if c1.button("Step (1 ciclo)"):
    sim.step_cycle()
    sim.committed += 0  # já atualizado no commit()
if c2.button(f"Rodar {runN} ciclos"):
    for _ in range(int(runN)):
        if sim.halted:
            break
        sim.step_cycle()
if c3.button("Rodar até HALT", type="secondary"):
    safety = 10000
    while not sim.halted and safety > 0:
        sim.step_cycle()
        safety -= 1

# Métricas
st.subheader("Métricas")
metrics = sim.metrics()
# Atualiza commits reais (contados no commit())
# (Já são refletidos em sim.committed quando commit() é chamado; garantimos consistência)
st.write(metrics)

# Visualizações de estado
st.markdown("---")

colA, colB = st.columns(2)
with colA:
    st.markdown("### ROB")
    rob_rows = []
    for i, e in enumerate(sim.rob):
        if e is None:
            rob_rows.append({"idx": i, "state": "-", "instr": "-", "dest": "-", "ready": "-", "value": "-", "mispred": "-"})
        else:
            rob_rows.append({
                "idx": i,
                "state": e.state,
                "instr": str(e.instr),
                "dest": f"R{e.dest_arch}" if e.dest_arch is not None else "-",
                "ready": e.ready,
                "value": e.value,
                "mispred": e.mispredict,
            })
    st.dataframe(rob_rows, use_container_width=True)

    st.markdown("### Estações de Reserva — ADD/SUB")
    st.dataframe([r.__dict__ for r in sim.RS_ADD], use_container_width=True)

    st.markdown("### Estações de Reserva — MUL/DIV")
    st.dataframe([r.__dict__ for r in sim.RS_MUL], use_container_width=True)

with colB:
    st.markdown("### Estações de Reserva — LD/ST")
    st.dataframe([r.__dict__ for r in sim.RS_LS], use_container_width=True)

    st.markdown("### Estações de Reserva — Branch")
    st.dataframe([r.__dict__ for r in sim.RS_BR], use_container_width=True)

    st.markdown("### Registradores arquiteturais (R0..R15)")
    regs = {f"R{i}": v for i, v in enumerate(sim.arch_regs)}
    st.dataframe([regs], use_container_width=True)

    st.markdown("### Mapa de Renomeação (reg -> ROB tag)")
    st.dataframe([sim.rename], use_container_width=True)

st.markdown("### Memória (primeiros 32 endereços)")
mem_view = {i: sim.memory[i] for i in range(32)}
st.dataframe([mem_view], use_container_width=True)

st.markdown("### Programa")
prog_tbl = [{"PC": i, "Instr": str(instr)} for i, instr in enumerate(sim.program)]
st.dataframe(prog_tbl, use_container_width=True)

st.markdown("### Log do ciclo atual")
if sim.events:
    for e in sim.events:
        st.write("• ", e)
else:
    st.write("(sem eventos)")

st.markdown("---")
st.caption("v1 — Este simulador é didático: conflitos no CDB são simplificados (1 writeback/ciclo), LD/ST não verificam dependências de aliasing e exceções de memória foram omitidas. Ideal para visualizar conceitos de Tomasulo, ROB e especulação.")

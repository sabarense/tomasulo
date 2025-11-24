# tomasulo_gui_light.py
# GUI em Tkinter/ttk (tema CLARO) para o simulador de Tomasulo
# Usa o núcleo em tomasulo_core.py

from __future__ import annotations

import copy
import tkinter as tk
from tkinter import ttk, messagebox
from tkinter.scrolledtext import ScrolledText

from tomasulo_core import TomasuloSim, assemble, DEFAULT_PROGRAM, NUM_REGS


class TomasuloApp(tk.Tk):
    def __init__(self):
        super().__init__()

        self.title("Simulador de Tomasulo — ROB + Especulação")
        self.geometry("1500x850")
        self.minsize(1300, 750)

        # Estado do simulador + histórico (Step Back)
        self.sim: TomasuloSim | None = None
        self.history: list[TomasuloSim] = []
        self.history_pos: int = -1

        # Estilo ttk (tema claro customizado)
        self.style = ttk.Style(self)
        self._configure_theme()

        # Variáveis dos cards
        self.var_cycle = tk.StringVar(value="0")
        self.var_ipc = tk.StringVar(value="0.000")
        self.var_commits = tk.StringVar(value="0")

        # Variáveis dos widgets principais
        self.rob_tree = None
        self.rs_add_tree = None
        self.rs_mul_tree = None
        self.rs_ls_tree = None
        self.rs_br_tree = None
        self.regs_tree = None
        self.rename_tree = None
        self.mem_tree = None
        self.prog_tree = None
        self.asm_text = None
        self.log_text = None

        # N ciclos
        self.runN_var = tk.IntVar(value=10)

        # Status
        self.status_var = tk.StringVar(value="Pronto")

        # Monta a interface
        self._build_ui()

        # Inicializa simulador
        self.on_reset()

    # ====================================================
    # Tema CLARO customizado
    # ====================================================
    def _configure_theme(self):
        # base do ttk
        self.style.theme_use("clam")

        bg_main = "#f3f4f6"      # fundo geral (cinza claro)
        bg_panel = "#ffffff"     # painéis (branco)
        fg_text = "#111827"      # texto (preto-acinzentado)
        accent = "#2563eb"       # azul

        self.configure(bg=bg_main)

        # Frames/Labels
        self.style.configure("Main.TFrame", background=bg_main)
        self.style.configure("Panel.TFrame", background=bg_panel)
        self.style.configure("Panel.TLabelframe", background=bg_panel, foreground=fg_text)
        self.style.configure("Panel.TLabelframe.Label", background=bg_panel, foreground=fg_text)
        self.style.configure("TLabel", background=bg_main, foreground=fg_text, font=("Segoe UI", 10))
        self.style.configure("Card.TLabel", background=bg_panel, foreground=fg_text)

        # Botões - estilo base (se precisar em outros lugares)
        self.style.configure(
            "TButton",
            background=accent,
            foreground="#ffffff",
            font=("Segoe UI", 9)
        )
        self.style.map(
            "TButton",
            background=[("active", "#1d4ed8")]
        )

        # Estilos específicos para os botões de simulação
        # Reset (neutro)
        self.style.configure(
            "SimReset.TButton",
            background="#e5e7eb",
            foreground=fg_text,
            font=("Segoe UI", 9)
        )
        self.style.map(
            "SimReset.TButton",
            background=[("active", "#d1d5db")]
        )

        # Step Back (aviso - laranja)
        self.style.configure(
            "SimBack.TButton",
            background="#fed7aa",
            foreground="#7c2d12",
            font=("Segoe UI", 9, "bold")
        )
        self.style.map(
            "SimBack.TButton",
            background=[("active", "#fdba74")]
        )

        # Step (ação simples - azul)
        self.style.configure(
            "SimStep.TButton",
            background="#bfdbfe",
            foreground="#1d4ed8",
            font=("Segoe UI", 9, "bold")
        )
        self.style.map(
            "SimStep.TButton",
            background=[("active", "#93c5fd")]
        )

        # Run N (execução - verde)
        self.style.configure(
            "SimRunN.TButton",
            background="#bbf7d0",
            foreground="#166534",
            font=("Segoe UI", 9, "bold")
        )
        self.style.map(
            "SimRunN.TButton",
            background=[("active", "#86efac")]
        )

        # Run até HALT (ação pesada - vermelho)
        self.style.configure(
            "SimRunHalt.TButton",
            background="#fecaca",
            foreground="#7f1d1d",
            font=("Segoe UI", 9, "bold")
        )
        self.style.map(
            "SimRunHalt.TButton",
            background=[("active", "#fca5a5")]
        )

        # Treeview (tabelas)
        self.style.configure(
            "Treeview",
            background="#ffffff",
            fieldbackground="#ffffff",
            foreground=fg_text,
            rowheight=22,
            font=("Consolas", 9),
        )
        self.style.configure(
            "Treeview.Heading",
            background="#e5e7eb",
            foreground=fg_text,
            font=("Segoe UI", 9, "bold")
        )

    # ====================================================
    # Construção da interface
    # ====================================================
    def _build_ui(self):
        # Janela principal dividida em sidebar (esquerda) + área principal (direita)
        root_frame = ttk.Frame(self, style="Main.TFrame")
        root_frame.pack(fill=tk.BOTH, expand=True)
        root_frame.columnconfigure(0, weight=0)
        root_frame.columnconfigure(1, weight=1)
        root_frame.rowconfigure(0, weight=1)
        root_frame.rowconfigure(1, weight=0)

        # Sidebar
        self._build_sidebar(root_frame)

        # Área principal
        self._build_main_area(root_frame)

        # Barra de status
        statusbar = ttk.Label(root_frame, textvariable=self.status_var,
                              anchor="w", style="Card.TLabel")
        statusbar.grid(row=1, column=0, columnspan=2, sticky="we", padx=6, pady=4)

    # ---------------- Sidebar (controles + ASM) ----------------
    def _build_sidebar(self, parent: ttk.Frame):
        sidebar = ttk.Frame(parent, style="Panel.TFrame", padding=8)
        sidebar.grid(row=0, column=0, sticky="nsw")
        sidebar.rowconfigure(3, weight=1)
        sidebar.columnconfigure(0, weight=1)

        # Título
        title_lbl = ttk.Label(sidebar, text="Tomasulo Sim", font=("Segoe UI", 14, "bold"),
                              style="Card.TLabel")
        title_lbl.grid(row=0, column=0, sticky="w", pady=(0, 6))

        # Controles
        controls = ttk.LabelFrame(sidebar, text="Simulação",
                                  padding=6, style="Panel.TLabelframe")
        controls.grid(row=1, column=0, sticky="we", pady=(0, 6))
        for i in range(2):
            controls.columnconfigure(i, weight=1)

        self.btn_reset = ttk.Button(
            controls,
            text="⟲ Montar & Resetar",
            command=self.on_reset,
            style="SimReset.TButton"
        )
        self.btn_step_back = ttk.Button(
            controls,
            text="⏮ Step Back",
            command=self.on_step_back,
            style="SimBack.TButton"
        )
        self.btn_step = ttk.Button(
            controls,
            text="⏭ Step (1 ciclo)",
            command=self.on_step,
            style="SimStep.TButton"
        )
        self.btn_run = ttk.Button(
            controls,
            text="▶ Rodar N ciclos",
            command=self.on_runN,
            style="SimRunN.TButton"
        )
        self.btn_run_halt = ttk.Button(
            controls,
            text="⏩ Rodar até HALT",
            command=self.on_run_until_halt,
            style="SimRunHalt.TButton"
        )

        self.btn_reset.grid(row=0, column=0, columnspan=2, sticky="we", padx=2, pady=2)
        self.btn_step_back.grid(row=1, column=0, sticky="we", padx=2, pady=2)
        self.btn_step.grid(row=1, column=1, sticky="we", padx=2, pady=2)
        self.btn_run.grid(row=2, column=0, sticky="we", padx=2, pady=2)
        self.btn_run_halt.grid(row=2, column=1, sticky="we", padx=2, pady=2)

        # N ciclos
        n_frame = ttk.Frame(controls, style="Panel.TFrame")
        n_frame.grid(row=3, column=0, columnspan=2, sticky="we", pady=(6, 2))
        ttk.Label(n_frame, text="N ciclos:", style="Card.TLabel").pack(side=tk.LEFT)
        spinN = ttk.Spinbox(n_frame, from_=1, to=10000, width=6,
                            textvariable=self.runN_var)
        spinN.pack(side=tk.LEFT, padx=(4, 0))

        # Programa (ASM)
        asm_frame = ttk.LabelFrame(sidebar, text="Programa (ASM)",
                                   padding=4, style="Panel.TLabelframe")
        asm_frame.grid(row=3, column=0, sticky="nsew", pady=(6, 0))
        asm_frame.rowconfigure(0, weight=1)
        asm_frame.columnconfigure(0, weight=1)

        self.asm_text = ScrolledText(
            asm_frame,
            wrap=tk.NONE,
            font=("Consolas", 9),
            height=20,
            bg="#ffffff",
            fg="#111827",
            insertbackground="#111827",
            relief=tk.FLAT,
            borderwidth=0
        )
        self.asm_text.grid(row=0, column=0, sticky="nsew")
        self.asm_text.insert("1.0", DEFAULT_PROGRAM)

    # ---------------- Área principal ----------------
    def _build_main_area(self, parent: ttk.Frame):
        main = ttk.Frame(parent, style="Main.TFrame", padding=8)
        main.grid(row=0, column=1, sticky="nsew")
        main.rowconfigure(1, weight=1)
        main.rowconfigure(2, weight=1)
        main.columnconfigure(0, weight=1)

        # Topo: cards
        self._build_metric_cards(main)

        # Meio: ROB + RS
        self._build_exec_area(main)

        # Base: estado + memória + programa + log
        self._build_bottom_area(main)

    # Cards de métricas
    def _build_metric_cards(self, parent: ttk.Frame):
        cards = ttk.Frame(parent, style="Main.TFrame")
        cards.grid(row=0, column=0, sticky="we", pady=(0, 8))
        for i in range(3):
            cards.columnconfigure(i, weight=1)

        self._create_metric_card(cards, "Ciclo Atual", self.var_cycle, 0)
        self._create_metric_card(cards, "IPC", self.var_ipc, 1)
        self._create_metric_card(cards, "Commits", self.var_commits, 2)

    def _create_metric_card(self, parent, title: str, var: tk.StringVar, col: int):
        frame = ttk.Frame(parent, style="Panel.TFrame", padding=(10, 6))
        frame.grid(row=0, column=col, sticky="nesw", padx=4)
        ttk.Label(frame, text=title, style="Card.TLabel",
                  font=("Segoe UI", 9)).pack(anchor="w")
        ttk.Label(frame, textvariable=var, style="Card.TLabel",
                  font=("Segoe UI", 18, "bold")).pack(anchor="w")

    # Meio: ROB + RS
    def _build_exec_area(self, parent: ttk.Frame):
        exec_frame = ttk.Frame(parent, style="Main.TFrame")
        exec_frame.grid(row=1, column=0, sticky="nsew")
        exec_frame.columnconfigure(0, weight=1)
        exec_frame.columnconfigure(1, weight=1)
        exec_frame.rowconfigure(0, weight=1)

        # ROB
        rob_frame = ttk.LabelFrame(exec_frame, text="ROB (Reorder Buffer)",
                                   padding=4, style="Panel.TLabelframe")
        rob_frame.grid(row=0, column=0, sticky="nsew", padx=(0, 4))

        columns_rob = ("idx", "state", "instr", "dest", "ready", "value", "mispred")
        self.rob_tree = ttk.Treeview(
            rob_frame,
            columns=columns_rob,
            show="headings",
            height=12
        )
        for col, w in zip(columns_rob, (40, 70, 320, 60, 60, 180, 70)):
            self.rob_tree.heading(col, text=col.upper())
            anchor = "w" if col == "instr" else "center"
            self.rob_tree.column(col, width=w, anchor=anchor)
        self.rob_tree.pack(fill=tk.BOTH, expand=True)

        self.rob_tree.tag_configure("ready", background="#22c55e", foreground="white")
        self.rob_tree.tag_configure("normal", background="")

        # RS (4 tabelas agrupadas)
        rs_frame = ttk.LabelFrame(exec_frame, text="Reservation Stations (RS)",
                                  padding=4, style="Panel.TLabelframe")
        rs_frame.grid(row=0, column=1, sticky="nsew", padx=(4, 0))
        rs_frame.columnconfigure((0, 1), weight=1)
        rs_frame.rowconfigure((0, 1), weight=1)

        def create_rs_table(parent_rs, title, row, col):
            frame = ttk.LabelFrame(parent_rs, text=title,
                                   padding=2, style="Panel.TLabelframe")
            frame.grid(row=row, column=col, sticky="nsew", padx=2, pady=2)
            frame.rowconfigure(0, weight=1)
            frame.columnconfigure(0, weight=1)

            cols = ("idx", "busy", "op", "Vj", "Vk", "Qj", "Qk", "A", "dest", "rem")
            tree = ttk.Treeview(frame, columns=cols, show="headings", height=5)
            widths = (40, 50, 55, 80, 80, 40, 40, 55, 55, 50)
            for c, w in zip(cols, widths):
                tree.heading(c, text=c.upper())
                tree.column(c, width=w, anchor="center")
            tree.grid(row=0, column=0, sticky="nsew")

            tree.tag_configure("busy", background="#fed7aa")
            tree.tag_configure("idle", background="")

            return tree

        self.rs_add_tree = create_rs_table(rs_frame, "ADD / SUB", 0, 0)
        self.rs_mul_tree = create_rs_table(rs_frame, "MUL / DIV", 0, 1)
        self.rs_ls_tree = create_rs_table(rs_frame, "LOAD / STORE", 1, 0)
        self.rs_br_tree = create_rs_table(rs_frame, "BRANCH", 1, 1)

    # Base: estado + memória + programa + log
    def _build_bottom_area(self, parent: ttk.Frame):
        bottom = ttk.Frame(parent, style="Main.TFrame")
        bottom.grid(row=2, column=0, sticky="nsew", pady=(8, 0))
        bottom.columnconfigure(0, weight=1)
        bottom.columnconfigure(1, weight=1)
        bottom.rowconfigure(0, weight=1)
        bottom.rowconfigure(1, weight=1)

        # Estado (registradores + rename)
        state_frame = ttk.LabelFrame(bottom, text="Estado (Registradores + Renomeação)",
                                     padding=4, style="Panel.TLabelframe")
        state_frame.grid(row=0, column=0, sticky="nsew", padx=(0, 4), pady=(0, 4))
        state_frame.columnconfigure(0, weight=1)
        state_frame.columnconfigure(1, weight=1)
        state_frame.rowconfigure(0, weight=1)

        # Registradores
        regs_frame = ttk.Frame(state_frame, style="Panel.TFrame")
        regs_frame.grid(row=0, column=0, sticky="nsew", padx=(0, 2))
        cols_regs = ("reg", "value")
        self.regs_tree = ttk.Treeview(regs_frame, columns=cols_regs, show="headings", height=6)
        self.regs_tree.heading("reg", text="REG")
        self.regs_tree.heading("value", text="VALOR")
        self.regs_tree.column("reg", width=50, anchor="center")
        self.regs_tree.column("value", width=80, anchor="center")
        self.regs_tree.pack(fill=tk.BOTH, expand=True)

        # Rename
        rename_frame = ttk.Frame(state_frame, style="Panel.TFrame")
        rename_frame.grid(row=0, column=1, sticky="nsew", padx=(2, 0))
        cols_rename = ("reg", "tag")
        self.rename_tree = ttk.Treeview(rename_frame, columns=cols_rename, show="headings", height=6)
        self.rename_tree.heading("reg", text="REG")
        self.rename_tree.heading("tag", text="ROB TAG")
        self.rename_tree.column("reg", width=50, anchor="center")
        self.rename_tree.column("tag", width=80, anchor="center")
        self.rename_tree.pack(fill=tk.BOTH, expand=True)

        # Memória + Programa + Log
        right_bottom = ttk.Frame(bottom, style="Main.TFrame")
        right_bottom.grid(row=0, column=1, rowspan=2, sticky="nsew", padx=(4, 0))
        right_bottom.columnconfigure(0, weight=1)
        right_bottom.rowconfigure(0, weight=1)
        right_bottom.rowconfigure(1, weight=1)

        mem_frame = ttk.LabelFrame(right_bottom, text="Memória (0..31)",
                                   padding=4, style="Panel.TLabelframe")
        mem_frame.grid(row=0, column=0, sticky="nsew", pady=(0, 4))
        cols_mem = ("addr", "value")
        self.mem_tree = ttk.Treeview(mem_frame, columns=cols_mem, show="headings", height=6)
        self.mem_tree.heading("addr", text="ADDR")
        self.mem_tree.heading("value", text="VALOR")
        self.mem_tree.column("addr", width=60, anchor="center")
        self.mem_tree.column("value", width=80, anchor="center")
        self.mem_tree.pack(fill=tk.BOTH, expand=True)

        prog_frame = ttk.LabelFrame(bottom, text="Programa (PC -> Instrução)",
                                    padding=4, style="Panel.TLabelframe")
        prog_frame.grid(row=1, column=0, sticky="nsew", padx=(0, 4), pady=(4, 0))
        cols_prog = ("pc", "instr")
        self.prog_tree = ttk.Treeview(prog_frame, columns=cols_prog, show="headings", height=6)
        self.prog_tree.heading("pc", text="PC")
        self.prog_tree.heading("instr", text="INSTRUÇÃO")
        self.prog_tree.column("pc", width=40, anchor="center")
        self.prog_tree.column("instr", width=260, anchor="w")
        self.prog_tree.pack(fill=tk.BOTH, expand=True)

        log_frame = ttk.LabelFrame(right_bottom, text="Log de Eventos (ciclo atual)",
                                   padding=4, style="Panel.TLabelframe")
        log_frame.grid(row=1, column=0, sticky="nsew", pady=(4, 0))
        self.log_text = ScrolledText(
            log_frame,
            wrap=tk.WORD,
            font=("Consolas", 9),
            height=6,
            bg="#ffffff",
            fg="#111827",
            insertbackground="#111827",
            relief=tk.FLAT,
            borderwidth=0
        )
        self.log_text.pack(fill=tk.BOTH, expand=True)

        # Tags coloridas no log
        self.log_text.tag_configure("issue", foreground="#0369a1")
        self.log_text.tag_configure("exec", foreground="#b45309")
        self.log_text.tag_configure("commit", foreground="#15803d")
        self.log_text.tag_configure("default", foreground="#111827")

    # ====================================================
    # Histórico (Step Back)
    # ====================================================
    def reset_history(self):
        self.history = []
        self.history_pos = -1
        if self.sim is not None:
            self.push_history_snapshot()

    def push_history_snapshot(self):
        if self.sim is None:
            return
        if 0 <= self.history_pos < len(self.history) - 1:
            self.history = self.history[: self.history_pos + 1]
        self.history.append(copy.deepcopy(self.sim))
        self.history_pos = len(self.history) - 1
        self.update_step_back_state()

    def can_step_back(self) -> bool:
        return self.history_pos > 0

    def update_step_back_state(self):
        state = tk.NORMAL if self.can_step_back() else tk.DISABLED
        self.btn_step_back.configure(state=state)

    # ====================================================
    # Log com cores
    # ====================================================
    def _set_log(self, text: str):
        self.log_text.configure(state=tk.NORMAL)
        self.log_text.delete("1.0", tk.END)
        lines = text.splitlines() if text else []
        if not lines:
            self.log_text.insert(tk.END, "(sem eventos neste ciclo)\n", "default")
        else:
            for line in lines:
                tag = "default"
                up = line.upper()
                if "ISSUE" in up:
                    tag = "issue"
                elif "EXEC" in up:
                    tag = "exec"
                elif "COMMIT" in up:
                    tag = "commit"
                self.log_text.insert(tk.END, line + "\n", tag)
        self.log_text.configure(state=tk.DISABLED)

    # ====================================================
    # Callbacks de simulação
    # ====================================================
    def on_reset(self):
        prog_text = self.asm_text.get("1.0", tk.END)
        try:
            program = assemble(prog_text)
        except Exception as e:
            messagebox.showerror("Erro na montagem", str(e))
            return

        lat = {
            "ADD": 2,
            "SUB": 2,
            "MUL": 8,
            "DIV": 16,
            "LD": 3,
            "ST": 3,
            "BEQ": 1,
            "BNE": 1,
            "NOP": 1,
            "HALT": 1,
        }
        sizes = {
            "RS_ADD": 4,
            "RS_MUL": 3,
            "RS_LS": 4,
            "RS_BR": 2,
            "ROB": 16,
        }

        self.sim = TomasuloSim(program, lat, sizes)

        # Estado inicial didático
        self.sim.arch_regs = [0] * NUM_REGS
        if NUM_REGS > 1:
            self.sim.arch_regs[1] = 10
        if NUM_REGS > 2:
            self.sim.arch_regs[2] = 20
        self.sim.memory[0] = 5

        self.reset_history()
        self.refresh_all()
        self.status_var.set("Simulador resetado")

    def on_step(self):
        if self.sim is None:
            return
        self.sim.step_cycle()
        self.push_history_snapshot()
        self.refresh_all()
        self.status_var.set("Step executado")

    def on_runN(self):
        if self.sim is None:
            return
        try:
            n = int(self.runN_var.get())
        except ValueError:
            messagebox.showwarning("Valor inválido", "Digite um número inteiro para N ciclos.")
            return

        for _ in range(n):
            if self.sim.halted:
                break
            self.sim.step_cycle()
            self.push_history_snapshot()
        self.refresh_all()
        self.status_var.set(f"Rodado N ciclos (N={n})")

    def on_run_until_halt(self):
        if self.sim is None:
            return
        safety = 10000
        while not self.sim.halted and safety > 0:
            self.sim.step_cycle()
            self.push_history_snapshot()
            safety -= 1
        self.refresh_all()
        self.status_var.set("Rodado até HALT ou limite de segurança")

    def on_step_back(self):
        if not self.can_step_back():
            return
        self.history_pos -= 1
        self.sim = copy.deepcopy(self.history[self.history_pos])
        self.update_step_back_state()
        self.refresh_all()
        self.status_var.set("Voltado um ciclo (Step Back)")

    # ====================================================
    # Atualização visual
    # ====================================================
    def refresh_all(self):
        if self.sim is None:
            return

        metrics = self.sim.metrics()
        ciclo = metrics.get("Ciclos", self.sim.cycle)
        ipc = metrics.get("IPC", 0.0)
        commits = metrics.get("Commits", 0)

        self.var_cycle.set(str(ciclo))
        self.var_ipc.set(f"{ipc:.3f}")
        self.var_commits.set(str(commits))

        self._fill_rob()
        self._fill_rs()
        self._fill_regs()
        self._fill_rename()
        self._fill_mem()
        self._fill_prog()

        log_str = "\n".join(self.sim.events) if self.sim.events else ""
        self._set_log(log_str)

        self.update_step_back_state()

    def _fill_rob(self):
        self.rob_tree.delete(*self.rob_tree.get_children())
        for i, e in enumerate(self.sim.rob):
            if e is None:
                vals = (i, "-", "-", "-", "-", "-", "-")
                tags = ("normal",)
            else:
                dest = f"R{e.dest_arch}" if e.dest_arch is not None else "-"
                val_str = str(e.value)
                if len(val_str) > 22:
                    val_str = val_str[:19] + "..."
                vals = (e.idx, e.state, str(e.instr), dest, e.ready, val_str, e.mispredict)
                tags = ("ready",) if e.ready else ("normal",)
            self.rob_tree.insert("", tk.END, values=vals, tags=tags)

    def _fill_rs(self):
        def fill(tree, table):
            tree.delete(*tree.get_children())
            for idx, rs in enumerate(table):
                busy = rs.busy
                vals = (
                    idx,
                    busy,
                    rs.op or "",
                    rs.Vj if not isinstance(rs.Vj, tuple) else str(rs.Vj),
                    rs.Vk if rs.Vk is not None else "",
                    rs.Qj if rs.Qj is not None else "",
                    rs.Qk if rs.Qk is not None else "",
                    rs.A if rs.A is not None else "",
                    rs.dest_tag if rs.dest_tag is not None else "",
                    rs.remaining,
                )
                tag = ("busy",) if busy else ("idle",)
                tree.insert("", tk.END, values=vals, tags=tag)

        fill(self.rs_add_tree, self.sim.RS_ADD)
        fill(self.rs_mul_tree, self.sim.RS_MUL)
        fill(self.rs_ls_tree, self.sim.RS_LS)
        fill(self.rs_br_tree, self.sim.RS_BR)

    def _fill_regs(self):
        self.regs_tree.delete(*self.regs_tree.get_children())
        for i, v in enumerate(self.sim.arch_regs):
            self.regs_tree.insert("", tk.END, values=(f"R{i}", v))

    def _fill_rename(self):
        self.rename_tree.delete(*self.rename_tree.get_children())
        for reg, tag in self.sim.rename.items():
            self.rename_tree.insert("", tk.END, values=(f"R{reg}", "-" if tag is None else tag))

    def _fill_mem(self):
        self.mem_tree.delete(*self.mem_tree.get_children())
        for addr in range(32):
            self.mem_tree.insert("", tk.END, values=(addr, self.sim.memory[addr]))

    def _fill_prog(self):
        self.prog_tree.delete(*self.prog_tree.get_children())
        for i, instr in enumerate(self.sim.program):
            self.prog_tree.insert("", tk.END, values=(i, str(instr)))

    # ====================================================
    # Run
    # ====================================================
    def run(self):
        self.mainloop()


if __name__ == "__main__":
    app = TomasuloApp()
    app.run()

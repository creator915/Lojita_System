<p align="center">
  <img src="./assets/logo.svg" width="112" height="112" alt="Lojita System Logo" />
</p>

<h1 align="center">Lojita System</h1>

<p align="center">
  <strong>Categorical Programming for the Post-Agent Era.</strong><br/>
  <em>Files are the ontology. Types are the rails. LLMs are just replaceable oracles.</em>
</p>

<p align="center">
  <em>Vibe Coding scales to toys. Categorical Programming scales to systems.</em>
</p>

<p align="center">
  <a href="../README.md">简体中文</a> ·
  <a href="./README_EN.md"><strong>English</strong></a> ·
  <a href="./MANIFESTO.md"><strong>📖 Full Architecture Manifesto (CN)</strong></a>
</p>

<p align="center">
  <img src="https://img.shields.io/badge/Kernel-Agda_2.6.3_(--safe)-0F172A?style=flat-square&logoColor=white" alt="Agda 2.6.3 --safe" />
  <img src="https://img.shields.io/badge/Fast_Backend-Lean_4_C%2B%2B_%2F_LCNF-2563EB?style=flat-square" alt="Lean 4 Backend" />
  <img src="https://img.shields.io/badge/Soundness-Zero--Axiom_Guard_(0_False_Positives)-10B981?style=flat-square" alt="Zero Axiom Guard" />
  <img src="https://img.shields.io/badge/BYOA-Works_with_Claude_Code_%26_Codex_CLI-FF2E54?style=flat-square" alt="Works with Claude Code & Codex" />
</p>

<p align="center">
  <img src="./assets/hero-loop.svg" width="960" alt="Lojita System Closed-Loop Execution" />
</p>

---

## ⚡ Beyond Humanoid Agents & Vibe Coding

Most AI coding tools anthropomorphize LLMs into chatty interns sitting at a Bash prompt (*CoT → ReAct → Multi-Agent*). Once a codebase grows past a few thousand lines, context windows rot, specifications drift, and agents silently weaken tests to make builds green.

**Lojita System is not another agent wrapper—it is a file-ontological formal operating system.** One session corresponds to one wish. Even Lojita's own probing scripts and scheduling state machines are machine-checked Agda programs, while LLMs serve purely as stateless, replaceable local oracles.

| Dimension | Vibe Coding / Humanoid Agents | Lojita System (Categorical Programming) |
| :--- | :--- | :--- |
| **Memory & Scale** | One bloated chat log mixes exploration noise, compiler spam, and global state | **File-Attached Local Memory**: Zero resident agent processes between wakeups; draft retries vanish in ephemeral slots, persisting only verified semantic causality |
| **Authority & Safety** | Blind `bash` / `sed` mutations over an untyped filesystem | **Linear Ownership Tree (No `write`)**: `File = Resource ⊗ !Data`; out-of-scope paths cannot even be constructed at the type level |
| **Decomposition** | Natural-language telephone game loses edge cases across sub-agents | **Prior Dialectica Gluing**: Before waking any child, the parent must machine-prove `ChildSpecs ∧ Parent ⊢ ParentSpec` |
| **Debugging & Evolution** | Manual firefighting, hardcoded literal hacks, or full rewrites | **Formal `: ⊥` Refutation & 0-Turn Reuse**: Impossible specs return closed `: ⊥` proofs; narrow gates emit `DETOUR` certificates; innocent subtrees reuse with **0 LLM calls** |

---

## 🧩 What Is Categorical Programming? (In 30 Seconds)

<table>
  <tr>
    <td width="33%" valign="top">
      <h3>1. Wire</h3>
      <p><strong>Plug typed ports, not prompts.</strong></p>
      <p>Modules live in a <strong>Colored Polycategory</strong>. Connecting an output port to an input port (<code>cut</code>) locks cross-module invariants at compile time. Writing a program is constructing a cut-preserving functor.</p>
    </td>
    <td width="33%" valign="top">
      <h3>2. Lift</h3>
      <p><strong>Solve a 5-point sandbox, then blow up.</strong></p>
      <p>Instead of drowning in hundreds of edge cases at once, prove the architecture over a tiny finite blueprint (<code>T0</code>), then apply <code>El</code> to blow up each base value into a rich fiber category (<code>T1</code>).</p>
    </td>
    <td width="33%" valign="top">
      <h3>3. Refute &amp; Transport</h3>
      <p><strong>Throw a <code>: ⊥</code> red card; keep innocent work.</strong></p>
      <p>When a sandbox shortcut fails to lift, the child submits a verified <code>: ⊥</code> proof to refactor <code>T0 ⇝ T0'</code>. Symmetric poly-profunctors transport architecture while sealing and reusing untouched subtrees at <strong>0 token cost</strong>.</p>
    </td>
  </tr>
</table>

---

## 🔌 Bring Your Own Agent: Tame Claude Code & Codex CLI

**Keep your existing Claude Code or Codex CLI subscription—zero ToS-breaking reverse engineering required.**

Frontier labs bundle their strongest models and quotas inside proprietary CLI agents. Lojita plugs them directly into `Code/AI.agda` while caging them inside a strict formal harness:
- **Zero Host Shell / Write Authority**: Launched in isolated read-only directories with built-in shell and autonomous sub-agent spawning disabled;
- **Millisecond Read-Only Oracles (MCP)**: Exposes zero-side-effect Lean 4 / Agda pre-checkers (`check_agda`, `check_plan`);
- **More Information, Never More Permission (0 False Positives)**: Soundness gates never compromise; when an AI hits a conservative syntactic gate (false negative), Lojita returns a structured **`DETOUR` certificate** (`[KIND] · [WITNESS] · [CAUSE] · [DETOUR]`) so the model routes around it in lines.

---

## 🌌 One Machine: From Large-Scale Software to Classic Theorems

Software looks *"sprawling yet locally routine"* because its multi-system boundaries are explicit; famous mathematical theorems look *"deceptively concise yet unfathomably deep"* only because they state acceptance specs inside a single rigid root world (`ℤ`) while hiding the cross-world categorical architecture. In Lojita, both run on the **exact same 2D categorical state machine**:

| 2D Categorical Machine | Large-Scale Software (e.g., Markdown Converter) | Classic Mathematics (e.g., Roth's Theorem on 3-APs) |
| :--- | :--- | :--- |
| **Root World Spec $E$** | End-to-end document conversion & world-coupled `∀ SimWorld` laws | Every positive-density subset of $(\mathbb{Z}, +)$ contains $x, x+d, x+2d$ |
| **Base Sandbox $T_0$** | Forget strings to a finite block-tag enum blueprint | Degenerate to finite field $\mathbb{F}_3^n$ (Meshulam sandbox: zero boundary leakage, ms counterexamples) |
| **Fiber Blow-Up (`El`)** | Heading tag blows up to `Fin 6` depth category; coarse step splits into parse + render | Exact subspace point $H$ blows up to multi-scale **Bohr set category** $\mathcal{B}(S, \rho)$ |
| **`: ⊥` Refutation & 0-Turn Reuse** | Single-pass $T_0$ drops reference links $\to$ `: ⊥` triggers 2-pass $T_0'$, **reusing `Escape₁` in 0 LLM turns** | Global shift $H+h=H$ fails on Bohr sets $\to$ `: ⊥` triggers regular narrow/wide pair $T_0'$, **reusing Parseval energy lemmas in 0 turns** |

---

## 🚀 Quick Start & Deep Dive

> See **[Build, Configuration & Usage Guide (QUICKSTART.md)](./QUICKSTART.md)** for full Linux toolchain setup, `./build.sh`, AI backend configuration (`Code/AI.agda`), and v7 offline regression suites.

- **Full Manifesto & Theoretical Whitepaper**: [docs/MANIFESTO.md](./MANIFESTO.md)
- **Unified Theory Outline**: [THEORY_UNIFIED.md](./THEORY_UNIFIED.md) · [TYPED_COLLAGE_FUNCTORS.md](./TYPED_COLLAGE_FUNCTORS.md)
- **2D Functorial Lift & `: ⊥` Recovery (v7)**: [V7_2D_LIFT_RECOVERY.md](./V7_2D_LIFT_RECOVERY.md)
- **Lean 4 Prism Dual-Kernel Backend**: [LEAN4_PRISM_BACKEND.md](./LEAN4_PRISM_BACKEND.md)
- **WebOperad Canvas Workbench (0-JS UI)**: [WEB_OPERAD.md](./WEB_OPERAD.md)
- **Linear Ownership Kernel**: [OWNERSHIP.md](./OWNERSHIP.md)
- **License**: [Apache License 2.0](../LICENSE)

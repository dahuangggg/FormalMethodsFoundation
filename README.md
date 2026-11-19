# FormalMethodsFoundation

[中文](#中文) | [English](#english)

---

## 中文

《形式化方法基础》课程作业与练习代码：表达式解析、集合/关系/文法等离散数学工具、Z3 SMT 求解器练习以及 Coq 证明示例。

### 状态

早期项目，不再维护。

### 功能

- **lab1-code**：四则运算表达式解析器（词法分析 + 递归下降语法分析，支持 `+ - * / ()`），生成 AST 并求值；附 Python 与 Z3 热身脚本。
- **lab2-code**：Z3 入门示例（命题逻辑、谓词逻辑等），以及将 Z3 表达式格式化输出的 `pretty_print`。
- **lab3-code**：基于 Z3 的 SAT 练习（DPLL、电路布局、N 皇后、座位安排等），部分文件仍为未完成的 TODO。
- **code**：课堂示例 —— 真值表与命题证明、幂集与子集和、关系性质（自反/对称/传递）、函数的 map/lambda 实现、玩具文法推导与解析，以及 Coq 求和公式证明 `Sum.v`。

### 技术栈

- Python ≥ 3.12，依赖由 [uv](https://docs.astral.sh/uv/) 管理（`pyproject.toml` / `uv.lock`）
- [z3-solver](https://github.com/Z3Prover/z3)
- Coq（仅 `code/Sum.v`，可在 <https://coq.vercel.app/scratchpad.html> 在线运行）

### 本地运行

```bash
uv sync

# 脚本会导入同目录模块，需先进入对应目录
cd lab1-code
uv run python z3_warmup.py
uv run python parser.py      # 解析并计算示例表达式
```

其他脚本同理，例如 `cd code && uv run python subset_sum.py`。

### 目录结构

```
.
├── lab1-code/      # 表达式解析器、Python/Z3 热身
├── lab2-code/      # Z3 入门与表达式美化输出
├── lab3-code/      # Z3 SAT 练习（DPLL、N 皇后等）
├── code/           # 课堂示例（集合、关系、文法、真值表、Coq）
├── main.py         # uv 项目模板入口
└── pyproject.toml
```

---

## English

Coursework and exercises for a *Foundations of Formal Methods* course: an expression parser, discrete-math utilities (sets, relations, grammars), Z3 SMT solver exercises, and a Coq proof example.

### Status

Early project, no longer actively maintained.

### Features

- **lab1-code**: arithmetic expression parser (lexer + recursive-descent parser for `+ - * / ()`) that builds an AST and evaluates it; plus Python and Z3 warm-up scripts.
- **lab2-code**: Z3 introduction examples (propositional and predicate logic) and a `pretty_print` formatter for Z3 expressions.
- **lab3-code**: Z3-based SAT exercises (DPLL, circuit layout, N-queens, seat arrangement, etc.); several files are still unfinished TODOs.
- **code**: lecture examples — truth tables and propositional proving, powerset and subset sum, relation properties (reflexive/symmetric/transitive), map- and lambda-backed functions, toy grammar derivation/parsing, and a Coq sum-formula proof in `Sum.v`.

### Tech Stack

- Python ≥ 3.12, dependencies managed with [uv](https://docs.astral.sh/uv/) (`pyproject.toml` / `uv.lock`)
- [z3-solver](https://github.com/Z3Prover/z3)
- Coq (only `code/Sum.v`; runnable online at <https://coq.vercel.app/scratchpad.html>)

### Getting Started

```bash
uv sync

# scripts import sibling modules, so run them from their own directory
cd lab1-code
uv run python z3_warmup.py
uv run python parser.py      # parse and evaluate sample expressions
```

Other scripts work the same way, e.g. `cd code && uv run python subset_sum.py`.

### Directory Structure

```
.
├── lab1-code/      # expression parser, Python/Z3 warm-ups
├── lab2-code/      # Z3 intro and expression pretty-printer
├── lab3-code/      # Z3 SAT exercises (DPLL, N-queens, ...)
├── code/           # lecture examples (sets, relations, grammars, truth tables, Coq)
├── main.py         # uv project template entry point
└── pyproject.toml
```

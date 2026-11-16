# 归隐理论（差异论）—— Lean 4 形式化

归隐子（束闻旭）"归隐理论"核心公理系统的 Lean 4 + Mathlib 形式化。
本文档是 **`GuiyinCross.lean`（跨维对位架构）** 的完整说明，含全部定义与定理清单。

## 1. 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `Guiyin.lean` | 四件套（`LayerProjection`、能量守恒、塌缩、不可逆），单 Hilbert 空间层 | ✅ 编译通过，零 sorry |
| `GuiyinModel.lean` | `LayerProjection` 的具体有限维模型验证 | ✅ 编译通过，零 sorry |
| `GuiyinCross.lean` | **跨维对位架构**：三态层 + 台阶层 + 自主排序 + 跨轴一致性 | ✅ 编译通过，零 sorry |

## 2. 环境

- Lean 4 工具链 `4.36.0-rc1`（经 `elan` 管理，直接调用 `toolchains/4.36.0-rc1/bin`）
- Mathlib `v4.36.0-rc1`
- 编译命令：

```powershell
$tc = "$env:USERPROFILE\.elan\toolchains\4.36.0-rc1"
$env:PATH = "$tc\bin;$env:PATH"
Set-Location "$env:USERPROFILE\mathlib4"
& "$tc\bin\lake.exe" env lean "C:\Users\LENOVO\mathlib4\GuiyinCross.lean"
```

## 3. 架构分层

`GuiyinCross.lean` 分四层，自下而上：

```
① 三态层        Phase / StateQuant / Interference / commonDist / D
② 排序层        toRank / sortAgainst / sortAgainst_sorted（"智能体 = 自主排序"引擎）
③ 台阶层        DiffLadder / StepMap / D_step_self / D_step_symm / D_to_interference
④ 具体模型      toStep / concreteStepMap（把 commonDist 接到台阶）
⑤ 跨轴一致性    toStep_ge_of_le_lam / axis_no_contradiction（三态轴 ↔ 台阶轴）
```

**跨维对位**：`D(x, y)` 允许 `x : StateQuant m`、`y : StateQuant n` 且 `m ≠ n`，两者在
`commonDim = min m n` 上对齐比较。

## 4. 核心类型

| 名称 | 定义 | 说明 |
|---|---|---|
| `Phase` | `positive / negative / neutral` | 相位三态 |
| `StateQuant (n : ℕ)` | `val : Fin n → ℚ`，`phase : Phase` | n 维态量 |
| `Interference` | `constructive / destructive / orthogonal` | 三态对位结果（相长/相消/正交） |
| `DiffLadder (m : ℕ)` | `lam : Fin (m+1) → ℚ`（严格递减 `strictAnti`），`zero_step : lam m = 0` | 差异阶梯，索引 0 最高、m 为零台阶 |
| `StepMap (m : ℕ)` | `L : DiffLadder m`，`step : StateQuant k → StateQuant n → Fin (m+1)`，`self` / `symm` 公理 | 台阶映射（自反、对称是 D2 公理） |

## 5. 核心函数

| 名称 | 签名 | 说明 |
|---|---|---|
| `commonDim` | `ℕ → ℕ → ℕ` | `min m n` |
| `Fin.embedLeft` / `Fin.embedRight` | `Fin (min m n) → Fin m` / `→ Fin n` | 跨维对齐嵌入 |
| `commonDist` | `StateQuant m → StateQuant n → ℚ` | 跨维平方距离 |
| `D` | `StateQuant m → StateQuant n → ℚ → Interference` | 三态对位：`commonDist > δ → orthogonal`；否则按相位分相长/相消/正交 |
| `Dopt` | `… → ℚ → ℕ → Option Interference` | 维度差超 `gap` → `none`（"不对位"） |
| `Interference.toRank` | `Interference → ℕ` | 排序键：相长 0 < 正交 1 < 相消 2 |
| `sortAgainst` | `StateQuant n → List (StateQuant m) → ℚ → List (StateQuant m)` | 自主排序（跨维） |
| `metaSequence` | `ℕ → Type` | 元序列（时间步 → 态量列表） |
| `D_to_interference` | `StepMap m → StateQuant k → StateQuant n → Fin (m+1) → Interference` | 台阶派生三态：`j < τ_c → destructive`，`j > τ_c → constructive`，`j = τ_c → orthogonal` |
| `toStep` | `ℚ → DiffLadder m → Fin (m+1)` | 距离 → 台阶（"最小 `j` 使 `d ≥ lam j`"，无则 `m`） |
| `concreteStepMap` | `DiffLadder m → StepMap m` | 具体台阶映射 `toStep ∘ commonDist` |

> **D4 修正记录**：`D_to_interference` 的 `constructive`/`destructive` 标签曾与差异论 D4
> "低差异线性叠加、高差异差异爆炸"方向相反（`toStep` 使距离大 → 高台阶）。已交换标签，
> 使"高差异（`j < τ_c`）→ 相消"、"低差异（`j > τ_c`）→ 相长"。

## 6. 定理清单

### 6.1 三态层

| 定理 | 签名 | 含义 |
|---|---|---|
| `commonDist_self` | `commonDist x x = 0` | 自距离为零（D2 自差异性） |
| `commonDist_symm` | `commonDist x y = commonDist y x` | 跨维对称（经 `Nat.min_comm` 双射重排） |
| `D_self_constructive` | `0 ≤ δ → x.phase ≠ neutral → D x x δ = constructive` | 自反在 D 层的静态根基 |
| `D_symm` | `D x y δ = D y x δ` | D2 对称性在 D 层的完整形式（9 种相位组合） |

### 6.2 排序层

| 定理 | 签名 | 含义 |
|---|---|---|
| `sortAgainst_sorted` | `List.Pairwise (fun x y => (D x ref δ).toRank ≤ (D y ref δ).toRank) (sortAgainst ref candidates δ)` | 排序后干涉等级非递减（稳定性） |

### 6.3 台阶层

| 定理 | 签名 | 含义 |
|---|---|---|
| `D_step_self` | `S.step x x = ⟨m, Nat.lt_succ_self m⟩` | D2 自反（`D(x,x) = λ_m`，最低台阶） |
| `D_step_symm` | `S.step x y = S.step y x` | D2 对称 |
| `toStep_zero` | `toStep 0 L = ⟨m, Nat.lt_succ_self m⟩` | 零距离 → 零台阶（`λ_m = 0` 钉死在 `zero_step`） |
| `toStep_ge_of_le_lam` | `d ≤ L.lam τ → τ ≤ toStep d L` | 距离不超过台阶值 ⟹ 落在 τ 或更低台阶（辅助引理） |

### 6.4 跨轴一致性

| 定理 | 签名 | 含义 |
|---|---|---|
| `axis_no_contradiction` | `L.lam τ_c = δ → D x y δ = constructive → D_to_interference (concreteStepMap L) x y τ_c ≠ destructive` | 弱一致性：D 判相长 ⟹ 台阶轴绝不同时判相消 |

## 7. 设计约束

- **构造性**：全程无 `Classical.em`、无 `Classical.choose`，排序与判定用 `Nat.decLe` / `Nat.le_total` / `Nat.le_trans`。
- **ℚ 全程**：拒绝连续统，无 ℝ。
- **零 sorry**：所有定理均有完整证明。
- **跨维**：`m ≠ n` 合法。
- **公理 vs 模型分离**：`StepMap` 的 `self`/`symm` 是 D2 公理（抽象给定），`concreteStepMap` 是"从 `commonDist` 映射"的具体模型。

## 8. 已知边界

- **强等价 `D x y δ = D_to_interference … τ_c` 未证**：在 `h_phase`/`h_neutral`/`h_lam` 下，
  按 `commonDist` 分区间仍有两处不齐——`commonDist = δ`（D 判相长、台阶轴判正交）与
  `commonDist > lam(τ_c-1)`（D 判超阈正交、台阶轴判高差异相消）。这两处是"超阈=正交"与
  "高差异=相消"的语义分歧，需额外的桥梁假设，属待定设计决策。

## 9. 备份

干净快照见 `backup/` 目录：

- `backup/2026-10-29/GuiyinCross.lean` —— 跨维对位 + 台阶层（接口清理后）
- `backup/2026-10-29/GuiyinCross.v2.lean` —— 上者 + 排序稳定性

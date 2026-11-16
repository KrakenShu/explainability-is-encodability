import Mathlib

open scoped BigOperators

inductive Phase where
  | positive : Phase   -- 正
  | negative : Phase   -- 负
  | neutral  : Phase   -- 中性

structure StateQuant (n : ℕ) where
  val : Fin n → ℚ
  phase : Phase

inductive Interference where
  | constructive : Interference  -- 相长
  | destructive  : Interference  -- 相消
  | orthogonal   : Interference  -- 正交

def commonDim (m n : ℕ) : ℕ := min m n

def Fin.embedLeft {m n : ℕ} (i : Fin (min m n)) : Fin m :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left m n)⟩

def Fin.embedRight {m n : ℕ} (i : Fin (min m n)) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right m n)⟩

def commonDist {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : ℚ :=
  ∑ i : Fin (commonDim m n),
    (x.val (Fin.embedLeft i) - y.val (Fin.embedRight i)) ^ 2

def D {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : Interference :=
  if commonDist x y > δ then
    .orthogonal
  else
    match x.phase, y.phase with
    | .positive, .positive => .constructive
    | .negative, .negative => .constructive
    | .positive, .negative => .destructive
    | .negative, .positive => .destructive
    | _, _ => .orthogonal

-- 第二步 1：D 返回 Option，维度差超阈值 → none（“不对位”，不是错误）
def Dopt {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) (gap : ℕ) : Option Interference :=
  if Nat.dist m n > gap then
    none
  else
    some (D x y δ)

-- 第二步 2：三态全序等级（相长 0 < 正交 1 < 相消 2）
namespace Interference

def toRank : Interference → ℕ
  | .constructive => 0
  | .orthogonal   => 1
  | .destructive  => 2

end Interference

-- 等级可判定（构造性，用 Nat.decLe，不碰 Classical）
instance : DecidableRel (fun (a b : Interference) => a.toRank ≤ b.toRank) :=
  fun a b => Nat.decLe a.toRank b.toRank

-- 按与参考点的对位结果排序：相长排前，正交次之，相消最后（跨维，支持 m ≠ n）
def sortAgainst {m n : ℕ} (ref : StateQuant n) (candidates : List (StateQuant m)) (δ : ℚ) : List (StateQuant m) :=
  List.insertionSort (fun x y => (D x ref δ).toRank ≤ (D y ref δ).toRank) candidates

-- 定理：排序后的列表，干涉等级非递减（Pairwise）
-- haveI 必需：把 Std.Total/IsTrans 注册成 typeclass 实例，pairwise_insertionSort 才能自动找到
set_option linter.style.haveILetI false in
theorem sortAgainst_sorted {m n : ℕ} (ref : StateQuant n) (candidates : List (StateQuant m)) (δ : ℚ) :
    List.Pairwise (fun x y => (D x ref δ).toRank ≤ (D y ref δ).toRank) (sortAgainst ref candidates δ) := by
  let r := fun (x y : StateQuant m) => (D x ref δ).toRank ≤ (D y ref δ).toRank
  haveI : Std.Total r := ⟨fun x y => Nat.le_total ((D x ref δ).toRank) ((D y ref δ).toRank)⟩
  haveI : IsTrans (StateQuant m) r := ⟨fun a b c hxy hyz => Nat.le_trans hxy hyz⟩
  simpa [sortAgainst, r] using (List.pairwise_insertionSort r candidates)

-- 第二步 3：元序列（时间步 → 态量列表），只要求“能定义”
def metaSequence (n : ℕ) : Type := ℕ → List (StateQuant n)
-- 第一个构造性性质：自距离为零（commonDist x x = 0）
-- 对应差异论 D2 的自差异性（D(x, x) = 最低台阶）
theorem commonDist_self {n : ℕ} (x : StateQuant n) :
    commonDist x x = 0 := by
  unfold commonDist
  simp [commonDim, Fin.embedLeft, Fin.embedRight]
-- 跨维对称性：commonDist x y = commonDist y x（对应 D2 对称性 D(x,y)=D(y,x)）
-- 关键：Fin (min m n) 和 Fin (min n m) 通过 Nat.min_comm 双射重排，每项平方对称
theorem commonDist_symm {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    commonDist x y = commonDist y x := by
  unfold commonDist
  change (∑ i : Fin (min m n), (x.val (Fin.embedLeft i) - y.val (Fin.embedRight i)) ^ 2)
       = (∑ i : Fin (min n m), (y.val (Fin.embedLeft i) - x.val (Fin.embedRight i)) ^ 2)
  refine Finset.sum_bij (fun i _ => Fin.cast (Nat.min_comm m n) i) ?hi ?inj ?surj ?h
  · intro i _hi
    simp
  · intro a _ha b _hb h
    apply Fin.ext
    simpa [Fin.val_cast] using congrArg Fin.val h
  · intro b _hb
    refine ⟨Fin.cast (Nat.min_comm n m) b, by simp, ?_⟩
    simp
  · intro i _hi
    simp [Fin.embedLeft, Fin.embedRight]
    ring
-- 方向 2：自反性在 D 层的静态根基
-- 自己和自己对位，δ ≥ 0 且相位非中性 ⟹ 相长
theorem D_self_constructive {m : ℕ} (x : StateQuant m) (δ : ℚ)
    (hδ : 0 ≤ δ) (hphase : x.phase ≠ Phase.neutral) :
    D x x δ = Interference.constructive := by
  -- 第 1 步：展开 D 的定义
  unfold D
  -- 第 2 步：commonDist x x = 0（依赖 commonDist_self）
  have hdist : commonDist x x = 0 := commonDist_self x
  rw [hdist]
  -- 第 3 步：由 hδ 得 ¬ (0 > δ)
  have hnot : ¬ (0 > δ) := not_lt_of_ge hδ
  -- 第 4 步：if 走 else 分支，进入相位判断
  rw [ite_eq_right hnot]
  -- 第 5 步：相位判断——positive/negative 都走相长分支，neutral 与 hphase 矛盾
  cases hx : x.phase with
  | positive => rfl
  | negative => rfl
  | neutral => exact (hphase hx).elim
-- 方向 1：跨维相位对称（D2 对称性 D(x,y)=D(y,x) 在 D 层的完整形式）
theorem D_symm {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    D x y δ = D y x δ := by
  -- 第 1 步：展开两边 D 的定义
  unfold D
  -- 第 2 步：用 commonDist_symm 把右边 commonDist y x 换成 commonDist x y
  have hdist : commonDist y x = commonDist x y := commonDist_symm y x
  rw [hdist]
  -- 第 3 步：按 commonDist x y > δ 分两路
  by_cases h : commonDist x y > δ
  · -- h 真：两边都走 then 分支 .orthogonal
    simp only [h, ite_true]
  · -- h 假：两边都走 else 分支，进入相位判断
    simp only [h, ite_false]
    -- 第 4 步：双层 cases 展开 9 种相位组合
    cases hx : x.phase with
    | positive =>
        cases hy : y.phase with
        | positive => rfl   -- 正/正 → 相长
        | negative => rfl   -- 正/负 → 相消
        | neutral => rfl    -- 正/中性 → 正交
    | negative =>
        cases hy : y.phase with
        | positive => rfl   -- 负/正 → 相消
        | negative => rfl   -- 负/负 → 相长
        | neutral => rfl    -- 负/中性 → 正交
    | neutral =>
        cases hy : y.phase with
        | positive => rfl   -- 中性/正 → 正交
        | negative => rfl   -- 中性/负 → 正交
        | neutral => rfl    -- 中性/中性 → 正交
-- ============ 台阶层（D2 原始形式）============

-- 第一步：差异阶梯，m+1 个台阶，索引 0 最高、m 最低（零台阶）
-- zero_step 把 λ_m = 0 钉死在定义里：零台阶即零差异，strictAnti 推出所有 j < m 的 lam j > 0
structure DiffLadder (m : ℕ) where
  lam : Fin (m+1) → ℚ
  strictAnti : ∀ i j : Fin (m+1), i < j → lam i > lam j
  zero_step : lam ⟨m, Nat.lt_succ_self m⟩ = 0

-- 第二步：台阶映射（抽象建模）
-- L 固化为字段，step 不再带 L 参数；自反和对称是 D2 的公理性质
structure StepMap (m : ℕ) where
  L : DiffLadder m
  step : {k n : ℕ} → StateQuant k → StateQuant n → Fin (m+1)
  self : ∀ {k} (x : StateQuant k), step x x = ⟨m, Nat.lt_succ_self m⟩
  symm : ∀ {k n} (x : StateQuant k) (y : StateQuant n), step x y = step y x

-- 第三步：D2 自反（D(x,x) = λ_m，最低台阶）
theorem D_step_self {m : ℕ} (S : StepMap m) {k : ℕ} (x : StateQuant k) :
    S.step x x = ⟨m, Nat.lt_succ_self m⟩ := S.self x

-- 第三步：D2 对称（D(x,y) = D(y,x)）
theorem D_step_symm {m : ℕ} (S : StepMap m) {k n : ℕ} (x : StateQuant k) (y : StateQuant n) :
    S.step x y = S.step y x := S.symm x y

-- 第四步：从台阶派生三态（用相变阈值 τ_c 分相）
-- j < τ_c（台阶高、索引小 = 高差异）→ 相消；j > τ_c（台阶低、索引大 = 低差异）→ 相长；j = τ_c → 正交
def D_to_interference {m k n : ℕ} (S : StepMap m) (x : StateQuant k) (y : StateQuant n)
    (τ_c : Fin (m+1)) : Interference :=
  let j := S.step x y
  if j < τ_c then Interference.destructive
  else if j > τ_c then Interference.constructive
  else Interference.orthogonal
-- ============ toStep：把 commonDist 接到台阶（从抽象 StepMap 到具体模型） ============

-- 给定距离 d 和阶梯 L，返回"最小台阶索引 j 使得 d ≥ lam j"；若无（d < lam m），返回最低台阶 m
def toStep {m : ℕ} (d : ℚ) (L : DiffLadder m) : Fin (m+1) :=
  match Fin.find? (fun j => decide (d ≥ L.lam j)) with
  | some j => j
  | none => ⟨m, Nat.lt_succ_self m⟩

-- 零距离映射到零台阶（用 L.zero_step，不再外部传 h_m）
theorem toStep_zero {m : ℕ} (L : DiffLadder m) :
    toStep 0 L = ⟨m, Nat.lt_succ_self m⟩ := by
  unfold toStep
  have hfind : Fin.find? (fun j => decide (0 ≥ L.lam j)) = some ⟨m, Nat.lt_succ_self m⟩ := by
    rw [Fin.find?_eq_some_iff]
    constructor
    · simp [L.zero_step]
    · intro j hj
      have hgt : L.lam j > 0 := by
        have h := L.strictAnti j ⟨m, Nat.lt_succ_self m⟩ hj
        simpa [L.zero_step] using h
      have hle : ¬ (0 ≥ L.lam j) := not_le_of_gt hgt
      simp [hle]
  rw [hfind]

-- 用 toStep ∘ commonDist 构造具体 StepMap（L 固化为字段，zero_step 自带）
def concreteStepMap {m : ℕ} (L : DiffLadder m) : StepMap m where
  L := L
  step x y := toStep (commonDist x y) L
  self x := by
    rw [commonDist_self]
    exact toStep_zero L
  symm x y := by
    rw [commonDist_symm]
-- ============ 方向 2：跨轴一致性 ============

-- 辅助引理：距离 d 不超过 τ 台阶值，则 toStep 落在 τ 或更低台阶（索引 ≥ τ）
lemma toStep_ge_of_le_lam {m : ℕ} (L : DiffLadder m) (d : ℚ) (τ : Fin (m+1))
    (hd : d ≤ L.lam τ) : τ ≤ toStep d L := by
  unfold toStep
  have hfalse : ∀ k : Fin (m+1), k < τ → decide (d ≥ L.lam k) = false := by
    intro k hk
    have hlam : L.lam k > L.lam τ := L.strictAnti k τ hk
    have hdlt : d < L.lam k := lt_of_le_of_lt hd hlam
    exact decide_eq_false_iff_not.mpr (not_le_of_gt hdlt)
  cases hf : Fin.find? (fun j => decide (d ≥ L.lam j)) with
  | none =>
      exact Fin.le_def.mpr (Nat.le_of_lt_succ τ.isLt)
  | some j =>
      rw [Fin.le_def]
      by_contra hlt
      have hltj : j.val < τ.val := Nat.lt_of_not_ge hlt
      have hpj : decide (d ≥ L.lam j) = true := (Fin.find?_eq_some_iff.mp hf).1
      have hpjfalse : decide (d ≥ L.lam j) = false := hfalse j (Fin.lt_def.mpr hltj)
      exact Bool.false_ne_true (hpj.symm.trans hpjfalse).symm

-- 跨轴弱一致性（不矛盾）：D 判相长（距离小、相位同号）⟹ 台阶轴绝不同时判相消
theorem axis_no_contradiction {m k n : ℕ} (x : StateQuant k) (y : StateQuant n)
    (δ : ℚ) (L : DiffLadder m) (τ_c : Fin (m+1))
    (h_lam : L.lam τ_c = δ) :
    D x y δ = Interference.constructive →
    D_to_interference (concreteStepMap L) x y τ_c ≠ Interference.destructive := by
  intro hD
  have hle : commonDist x y ≤ δ := by
    by_cases h : commonDist x y > δ
    · have horth : D x y δ = Interference.orthogonal := by
        unfold D
        simp [h]
      rw [horth] at hD
      cases hD
    · exact le_of_not_gt h
  have htoStep : τ_c ≤ toStep (commonDist x y) L :=
    toStep_ge_of_le_lam L (commonDist x y) τ_c (by simpa [h_lam] using hle)
  intro hDI
  simp only [D_to_interference] at hDI
  have hstep_ge : τ_c ≤ (concreteStepMap L).step x y := by
    simpa [concreteStepMap] using htoStep
  rw [ite_eq_right (not_lt_of_ge hstep_ge)] at hDI
  by_cases hgt : τ_c < (concreteStepMap L).step x y
  · simp only [hgt, ite_true] at hDI
    cases hDI
  · simp only [hgt, ite_false] at hDI
    cases hDI
-- ============ 记忆库与唤醒机制 ============

-- 记忆库：一组态量组成的有限列表（abbrev 让 MemoryLibrary 自动 reducible 到 List）
abbrev MemoryLibrary (n : ℕ) := List (StateQuant n)

-- 唤醒：给定参考点 ref，从库中挑出与它干涉结果最好（排在最前）的态量
def awaken {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) : Option (StateQuant m) :=
  match sortAgainst ref lib δ with
  | [] => none
  | best :: _ => some best

-- 定理：唤醒成功 ⟹ best 的干涉等级 ≤ 库里任何元素
set_option linter.style.haveILetI false in
theorem awaken_optimal {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) 
    (best : StateQuant m) (h_awaken : awaken lib ref δ = some best) :
    ∀ (x : StateQuant m), x ∈ lib → (D best ref δ).toRank ≤ (D x ref δ).toRank := by
  intro x hx
  unfold awaken at h_awaken
  cases hsort : sortAgainst ref lib δ with
  | nil => simp [hsort] at h_awaken
  | cons b rest =>
      simp [hsort] at h_awaken
      have hbest : b = best := h_awaken
      have hpair : List.Pairwise (fun a b => (D a ref δ).toRank ≤ (D b ref δ).toRank) (sortAgainst ref lib δ) :=
        sortAgainst_sorted ref lib δ
      rw [hsort] at hpair
      have hperm : List.Perm (sortAgainst ref lib δ) lib := by
        simpa [sortAgainst] using (List.perm_insertionSort (fun a b => (D a ref δ).toRank ≤ (D b ref δ).toRank) lib)
      have hx' : x ∈ sortAgainst ref lib δ := (List.Perm.mem_iff hperm).mpr hx
      rw [hsort] at hx'
      haveI : Std.Refl (fun (a b : StateQuant m) => (D a ref δ).toRank ≤ (D b ref δ).toRank) := ⟨fun (a : StateQuant m) => le_rfl⟩
      haveI : Inhabited (StateQuant m) := ⟨⟨fun _ => 0, Phase.neutral⟩⟩
      have hrel : (D b ref δ).toRank ≤ (D x ref δ).toRank :=
        List.Pairwise.head!_le hpair hx'
      simpa [hbest] using hrel
-- ============ 元序列演化与动力学 ============

-- 时间步更新：把新经历 ref 并入库中（δ 暂为哑参数，留待复杂融合逻辑）
def step {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (_δ : ℚ) : MemoryLibrary n :=
  ref :: lib

-- 演化序列：从初始库出发，逐时间步并入输入
def evolve {n : ℕ} (init_lib : MemoryLibrary n) (inputs : ℕ → StateQuant n) (δ : ℚ) : ℕ → MemoryLibrary n
  | 0 => init_lib
  | t + 1 => step (evolve init_lib inputs δ t) (inputs t) δ

-- 记忆保持：新的经历一定会被记住
theorem step_mem {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ) :
    ref ∈ step lib ref δ := by
  simp [step]

-- 演化记忆：第 t 个输入在第 t+1 时刻一定在库中
theorem evolve_mem {n : ℕ} (init_lib : MemoryLibrary n) (inputs : ℕ → StateQuant n) (δ : ℚ) (t : ℕ) :
    inputs t ∈ evolve init_lib inputs δ (t + 1) := by
  simp [evolve, step]
-- ============ 自我确认不动点定理（Ego Fixed-Point） ============

-- 若 ref 自反相长（rank 0），唤醒自己得到的还是自己
theorem awaken_self {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (_h_in : ref ∈ lib)
    (h_self : D ref ref δ = Interference.constructive) :
    awaken (step lib ref δ) ref δ = some ref := by
  have hrank : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  have hrel : ∀ b ∈ lib, (D ref ref δ).toRank ≤ (D b ref δ).toRank := by
    intro b hb
    rw [hrank]
    exact Nat.zero_le _
  have hcons : sortAgainst ref (ref :: lib) δ = ref :: sortAgainst ref lib δ := by
    unfold sortAgainst
    exact List.insertionSort_cons_of_forall_rel (fun a b => (D a ref δ).toRank ≤ (D b ref δ).toRank) hrel
  unfold awaken
  simp only [step]
  rw [hcons]
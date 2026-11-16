import Mathlib

open scoped BigOperators

/- ============ 离散流体微团框架（Fluid） ============
   抛弃连续统，用 ℚ 离散坐标 + 对位博弈，构建流体微团的生存动力学。
   速度不是绝对坐标系的 (u,v,w)，而是"生存博弈态"：遇到体量更大的流体，
   为不被吞没（夺舍），微团必须产生相对逃逸。
   全程 ℚ，无 ℝ，无 Classical，无微积分。 -/

-- 相位（三态，表示流向）
inductive Phase where
  | positive : Phase   -- 正
  | negative : Phase   -- 负
  | neutral  : Phase   -- 中性
  deriving DecidableEq

-- 干涉结果（三态：相长/相消/正交）
inductive Interference where
  | constructive : Interference  -- 相长
  | destructive  : Interference  -- 相消
  | orthogonal   : Interference  -- 正交

-- 离散流体微团
structure FluidParcel where
  pos : ℚ × ℚ        -- 位置 (x, y)
  mass : ℚ           -- 体量/质量（对应 normSq，代表不被吞没的底气）
  phase : Phase      -- 相位（流向）
  h_mass : mass > 0  -- 质量必须大于 0

-- 距离：欧氏距离的平方和（不开根号，保持 ℚ）
def fluidDist (p1 p2 : FluidParcel) : ℚ :=
  (p1.pos.1 - p2.pos.1)^2 + (p1.pos.2 - p2.pos.2)^2

-- 博弈判定：相遇时谁吞并谁
def collide (p1 p2 : FluidParcel) (threshold : ℚ) : Interference :=
  if fluidDist p1 p2 > threshold then
    .orthogonal          -- 距离太远，互不干扰
  else if p1.phase = p2.phase then
    .constructive        -- 同向，可以合并（体量大的主导）
  else
    .destructive         -- 反向，发生剪切/相消

-- 判断 a 是否会被 b 吞并
def will_be_absorbed (a b : FluidParcel) (threshold : ℚ) : Prop :=
  collide a b threshold = .constructive ∧ b.mass > a.mass

-- 逃逸操作：a 以速度 v 位移（状态跃迁）
def escape (a : FluidParcel) (v : ℚ × ℚ) : FluidParcel :=
  { a with pos := (a.pos.1 + v.1, a.pos.2 + v.2) }

-- 逃逸速度的必然性：只要给定足够大的逃逸速度，a 就能摆脱 b 的干涉范围
theorem escape_survival (a b : FluidParcel) (threshold : ℚ)
    (_h_absorb : will_be_absorbed a b threshold) :
    ∃ (v : ℚ × ℚ), fluidDist (escape a v) b > threshold := by
  -- 沿 x 方向把 a 推到 b 右侧 threshold + 1 处，距离变成 (threshold + 1)^2
  let v : ℚ × ℚ := (b.pos.1 - a.pos.1 + threshold + 1, b.pos.2 - a.pos.2)
  refine ⟨v, ?_⟩
  have hfluidDist : fluidDist (escape a v) b = (threshold + 1)^2 := by
    unfold fluidDist escape
    simp [v]
    ring
  rw [hfluidDist]
  -- (threshold + 1)^2 > threshold 恒成立（配平方：threshold² + threshold + 1 > 0）
  nlinarith [sq_nonneg (threshold + 1 / 2), show (0 : ℚ) < 3 / 4 by norm_num]

-- moveB：b 以速度 w 位移（追击）
def moveB (b : FluidParcel) (w : ℚ × ℚ) : FluidParcel :=
  { b with pos := (b.pos.1 + w.1, b.pos.2 + w.2) }

-- 追击定理（离散时间 t : ℕ）：
-- 一维追击：a 在原点沿 x 正向以 vx 逃逸，b 在 (vx+wx)*t0 处沿 x 负向以 wx 追击（wx > vx，b 更快）。
-- 初始距离 = 相对步长 (vx+wx) × t0，故 t0 时刻 b 恰好追上 a（fluidDist = 0）。
-- 体量不足、速度又慢，最终必定被吞没。
theorem cannot_escape_if_slower (a b : FluidParcel) (vx wx : ℚ) (t0 : ℕ) (threshold : ℚ)
    (h_apos : a.pos = (0, 0))
    (h_bpos : b.pos = ((vx + wx) * (t0 : ℚ), 0))
    (_h_vx : 0 < vx) (_h_wx : vx < wx)
    (hthr : 0 ≤ threshold) :
    ∃ t : ℕ, fluidDist (escape a ((t : ℚ) * vx, 0)) (moveB b (-((t : ℚ) * wx), 0)) ≤ threshold := by
  refine ⟨t0, ?_⟩
  have hpos_a : (escape a ((t0 : ℚ) * vx, 0)).pos = ((t0 : ℚ) * vx, 0) := by
    unfold escape
    simp [h_apos]
  have hpos_b : (moveB b (-((t0 : ℚ) * wx), 0)).pos = (((vx + wx) * (t0 : ℚ) - (t0 : ℚ) * wx), 0) := by
    unfold moveB
    simp [h_bpos]
    ring
  have hd : fluidDist (escape a ((t0 : ℚ) * vx, 0)) (moveB b (-((t0 : ℚ) * wx), 0)) = 0 := by
    unfold fluidDist
    simp [hpos_a, hpos_b]
    ring
  rw [hd]
  exact hthr
-- 正交逃逸：a 沿 y 轴正交逃逸，b 只能在 x 轴追击，两者 y 坐标永远差 (t+1)*vy > 0，永不重合。
-- 正交变向是面对同向高体量追击时的唯一活路。
theorem orthogonal_escape (a b : FluidParcel) (vy wx : ℚ) (t : ℕ)
    (h_apos : a.pos = (0, 0))
    (h_bpos : b.pos.2 = 0)          -- b 初始在 x 轴上（只能在 x 轴追）
    (h_vy : 0 < vy) :
    fluidDist (escape a (0, ((t + 1) : ℚ) * vy)) (moveB b (-((t + 1) : ℚ) * wx, 0)) > 0 := by
  have hdist : fluidDist (escape a (0, ((t + 1) : ℚ) * vy)) (moveB b (-((t + 1) : ℚ) * wx, 0)) =
      (b.pos.1 - ((t + 1) : ℚ) * wx)^2 + (((t + 1) : ℚ) * vy)^2 := by
    unfold fluidDist escape moveB
    simp [h_apos, h_bpos]
    ring
  rw [hdist]
  have htvy : ((t + 1) : ℚ) * vy > 0 := mul_pos (by exact_mod_cast (Nat.succ_pos t)) h_vy
  have hsq : 0 < (((t + 1) : ℚ) * vy)^2 := sq_pos_of_pos htvy
  -- 第一项（x 方向距离平方）≥ 0，第二项（y 方向）> 0，故和 > 0
  nlinarith [sq_nonneg (b.pos.1 - ((t + 1) : ℚ) * wx), hsq]
-- 阿基米德 + 最小性：存在 t 使得 s*t ∈ [d, d+s)（s > 0, d > 0）
lemma exists_nat_mul_interval {s d : ℚ} (hs : 0 < s) (hd : 0 < d) :
    ∃ t : ℕ, d ≤ s * (t : ℚ) ∧ s * (t : ℚ) < d + s := by
  have h_exist : ∃ t : ℕ, d ≤ s * (t : ℚ) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (d / s)
    refine ⟨n, le_of_lt ?_⟩
    nlinarith [(div_lt_iff₀ hs).mp hn]
  let t := Nat.find h_exist
  refine ⟨t, Nat.find_spec h_exist, ?_⟩
  have ht_pos : 0 < t := by
    by_contra h
    have h0 : t = 0 := Nat.eq_zero_of_not_pos h
    have hspec : d ≤ s * (t : ℚ) := Nat.find_spec h_exist
    rw [h0] at hspec
    have : d ≤ 0 := by simpa using hspec
    exact (not_le_of_gt hd) this
  have hprev : s * ((t - 1 : ℕ) : ℚ) < d := by
    have hmin : ¬ (d ≤ s * ((t - 1 : ℕ) : ℚ)) := Nat.find_min h_exist (Nat.pred_lt_self ht_pos)
    exact lt_of_not_ge hmin
  have hcast : ((t - 1 : ℕ) : ℚ) = (t : ℚ) - 1 := Nat.cast_pred ht_pos
  rw [hcast] at hprev
  nlinarith [hprev]

-- 真实追击：b 更快（wx > vx），存在 t 使得追上（距离平方 < 相对步长平方 (wx-vx)²）
theorem cannot_escape_general (a b : FluidParcel) (vx wx d threshold : ℚ)
    (h_apos : a.pos = (0, 0))
    (h_bpos : b.pos = (-d, 0))
    (h_d : 0 < d)
    (_h_vx : 0 < vx)
    (h_wx : vx < wx)
    (h_thr : (wx - vx)^2 ≤ threshold) :
    ∃ (t : ℕ), fluidDist (escape a ((t : ℚ) * vx, 0)) (moveB b ((t : ℚ) * wx, 0)) ≤ threshold := by
  let s := wx - vx
  have hs : 0 < s := sub_pos.mpr h_wx
  obtain ⟨t, ht_ge, ht_lt⟩ := exists_nat_mul_interval hs h_d
  refine ⟨t, ?_⟩
  have hdist : fluidDist (escape a ((t : ℚ) * vx, 0)) (moveB b ((t : ℚ) * wx, 0)) = (s * (t : ℚ) - d)^2 := by
    unfold fluidDist escape moveB
    simp [h_apos, h_bpos, s]
    ring
  rw [hdist]
  have hdiff_nonneg : 0 ≤ s * (t : ℚ) - d := sub_nonneg.mpr ht_ge
  have hdiff_lt : s * (t : ℚ) - d < s := by nlinarith [ht_lt]
  have hsq : (s * (t : ℚ) - d)^2 < s^2 := by
    nlinarith [hdiff_nonneg, hdiff_lt, hs]
  exact le_trans (le_of_lt hsq) h_thr

-- 绝对安全距离（Escape Beyond Threshold）：
-- 任意大的危险范围 threshold，只要正交逃逸速度 vy 足够大，必存在时刻双方距离平方严格超过 threshold。
-- 这才是"真正的安全"：orthogonal_escape 只证 > 0（没撞死），这里证 > threshold（安全区外）。
-- 关键：x 方向平方项 ≥ 0 恒成立，只需 y 方向 (t·vy)² 突破 threshold；
-- 由 t ≥ 1（h_t : 0 < t）与 vy = threshold + 1，得 (t·vy)² ≥ vy² = (threshold+1)² > threshold。
theorem orthogonal_escape_safe (a b : FluidParcel) (wx threshold : ℚ) (t : ℕ)
    (h_apos : a.pos = (0, 0))
    (h_bpos : b.pos.2 = 0)
    (h_t : 0 < t)
    (h_thr : 0 < threshold) :
    ∃ (vy : ℚ), vy > 0 ∧ fluidDist (escape a (0, (t : ℚ) * vy)) (moveB b (-((t : ℚ) * wx), 0)) > threshold := by
  let vy : ℚ := threshold + 1
  refine ⟨vy, ?_, ?_⟩
  · -- vy = threshold + 1 > 0
    nlinarith [h_thr]
  · -- 距离平方 > threshold
    have hdist : fluidDist (escape a (0, (t : ℚ) * vy)) (moveB b (-((t : ℚ) * wx), 0))
        = (b.pos.1 - (t : ℚ) * wx)^2 + ((t : ℚ) * vy)^2 := by
      unfold fluidDist escape moveB
      simp [h_apos, h_bpos]
      ring
    rw [hdist]
    have ht_ge : (1 : ℚ) ≤ (t : ℚ) := by
      exact_mod_cast (Nat.succ_le_of_lt h_t)
    have hvy_pos : 0 < vy := by nlinarith [h_thr]
    have hty_ge : vy ≤ (t : ℚ) * vy := by
      have h := mul_le_mul_of_nonneg_right ht_ge (le_of_lt hvy_pos)
      simpa using h
    have hsq_le : vy^2 ≤ ((t : ℚ) * vy)^2 :=
      pow_le_pow_left₀ (le_of_lt hvy_pos) hty_ge 2
    have hvy_sq_gt : vy^2 > threshold := by
      nlinarith [sq_nonneg threshold, h_thr]
    have hty_sq_gt : ((t : ℚ) * vy)^2 > threshold := by
      nlinarith [hsq_le, hvy_sq_gt]
    nlinarith [sq_nonneg (b.pos.1 - (t : ℚ) * wx), hty_sq_gt]

-- ============ 合并（Fusion）机制与质量守恒 ============
-- 相同相位的微团相撞会合并成一个更大的液滴，而非简单的"谁吞并谁"。

-- 合并算子：质量相加（守恒），位置取质心（按质量加权），相位继承 a。
def merge (a b : FluidParcel) : FluidParcel :=
  let new_mass := a.mass + b.mass
  let new_x := (a.mass * a.pos.1 + b.mass * b.pos.1) / new_mass
  let new_y := (a.mass * a.pos.2 + b.mass * b.pos.2) / new_mass
  { pos := (new_x, new_y),
    mass := new_mass,
    phase := a.phase,
    h_mass := by linarith [a.h_mass, b.h_mass] }

-- 质量守恒：合并后的体量恰为两者之和。
theorem merge_mass_conservation (a b : FluidParcel) :
    (merge a b).mass = a.mass + b.mass := by
  rfl

-- 合并即免疫（Fusion Immunity）：
-- a 被 b 威胁（b.mass > a.mass），与同质量盟友 c（c.mass = a.mass）合并，
-- 合并体量 = a.mass + c.mass = 2 * a.mass。
-- 只要威胁体量不超过翻倍体量（b.mass < 2 * a.mass），合并体就严格大于 b，从而免疫。
-- 注意：仅有 h_threat 与 h_ally 是不够的 —— 反例 a.mass = 1, b.mass = 100, c.mass = 1，
-- 此时 b > a 但 2a = 2 < 100 = b，翻倍仍无法反超。故必须补充 h_below_double 假设。
theorem fusion_immunity (a b c : FluidParcel)
    (_h_threat : b.mass > a.mass)
    (h_ally : c.mass = a.mass)
    (h_below_double : b.mass < 2 * a.mass) :
    (merge a c).mass > b.mass := by
  rw [merge_mass_conservation, h_ally]
  nlinarith

-- 合并后的生存（Fusion Survival）：一旦合并体体量严格大于 b，
-- 在后续对位中 b 再也无法吞并它（will_be_absorbed 的体量条件被打破）。
theorem fusion_survival (a b c : FluidParcel) (threshold : ℚ)
    (h_strong : (merge a c).mass > b.mass) :
    ¬ will_be_absorbed (merge a c) b threshold := by
  intro h
  have h2 : b.mass > (merge a c).mass := by
    unfold will_be_absorbed at h
    exact h.2
  nlinarith
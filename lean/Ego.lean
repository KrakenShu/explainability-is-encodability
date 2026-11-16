import Mathlib

open scoped BigOperators

/- ================================================================
   论文对应表
   ----------------------------------------------------------------
   本文件是「归隐理论」的完整形式化；其中一部分由论文
   《可解释性 = 可编码性》引用。对应关系如下（行号为定义位置）：

   §2   基础        StateQuant L178 · commonDist L197 · LayerLadder L4095
   §3   紧层论      ResLayer.condense L3961 · resolution L3982
   §4   判据        Coherent L9072 · layerState L10739
   §5   主定理      encode L9322 · interpretability_is_encodability L9364
   §6   gap 精确值  reluAffine L9544 · IsGap L9714
   §7   gap 延伸    gSep L10012 · unifGrid L10121 · sqDist L10504
   §8   b₁          eulerB1 L9447 · SquareFlat L10852

   A0/A1 自指公理  SelfRef L13035 · entropy L12973
                   ——定义在 §4–§8 之后，Lean 不允许前向引用，
                     故论文定理不依赖自指公理。

   其余区段（洞与澄明、对位、符号代数、守恒网络、topos、
   ⊕_D 分段代数等）属于未发表的其他工作，论文不引用。

   完整定理索引见论文附录 B。
   ================================================================ -/

/- ================================================================
   归隐理论（差异论）· 根
   ================================================================

   【唯一根：有限性】

   有限性是唯一根。差异、ℚ、分辨都不是根，是有限性的三张脸：
     · 差异 = 分辨的代名词（差异 = 一分为二 = 意识主体的动作）
     · ℚ     = 有限性发生的地方（代数 + 序，离散，拒连续统 ℝ）
     · 分辨  = 有限性的动作（resolveSpace = 一分为二 = 2^n）

   唯一的事实：n < 2^n（有限集严格小于其分辨空间）。

   【从唯一根长出一切】

   有限性自带构造能力——它逼出康托尔对角线，对角线逼出洞，洞逼出一切：

     ① 分辨（差异）     = 一分为二 2^n          —— resolveSpace / resolve_card
     ② 洞（无的正面身份）= 自指盲区（康托尔）    —— diagonal_hole / hole_reborn
     ③ 熵（洞的数量）   = 2^n − |像|            —— entropy / entropy_eq_blindSet_card
     ④ 熵增（不可磨灭）  = 堵一个生一个          —— hole_reborn / blindSpotBound 单调无上限
     ⑤ 自我（自己的洞）  = 认领自指的洞          —— self_is_hole
     ⑥ 态射（定向差异）  = 分辨的族（函数性）    —— morphismToResolves ⟷ functionalToMorphism
     ⑦ 对称（守恒+向量） = S_n 直和分解          —— symmetrize / antisymmetrize（Noether 有限版）
     ⑧ 差异对象（洞度量） = s / r / n            —— DifferenceObject
     ⑨ 智能（调节洞）    = 单调收敛             —— reflect / reflectStep
     ⑩ 稳定（洞的平衡）  = s/r = n 不动点        —— reflect_fixed_point_iff_stable
     ⑪ 阈值（有限 ⇒ 台阶） = 从有限集合逼出       —— δThreshold / diffSupport / τ_c
     ⑫ 合成（差异运算）   = 四相 ⊕_D             —— composeD4 / cycleCompose
     ⑬ 观测 ≡ 管理        = 规则族与阈值族互为参数化 —— observation_is_management
     ⑭ 一般分类器边界     = 读数塌缩成基数          —— general_classifier_boundary
     ⑮ 读数 = 谱的层析     = 三界读数就是 barcode     —— readings_determine_spectrum
     ⑯ 完整持久同调       = birth（谱）+ death（合并） —— full_persistence
     ⑰ 分段代数           = ⊕_D 的幂等域/结合区/幽灵   —— segmented_algebra
     ⑱ 总量完全性         = 任何不变量都是总量的函数   —— total_is_complete_invariant
     ⑲ 阈值族 = 规则族的上闭部分 —— threshold_iff_upward_closed
     ⑳ Mittag-Leffler 坍缩 = 满射塔极限平凡             —— mittag_leffler_collapse
     ㉑ 多参数入口         = 一维投影不决定二维         —— point_projection_not_sufficient
     ㉒ D_typed 一维性     = min + 平方和双重压缩       —— typed_is_one_dimensional
     ㉓ 真二维不可分解     = Casson–Zomorodian 反例     —— cz_not_interval_decomposable
     ㉔ 判别线             = Möbius 非负 ⟺ 可分解       —— constant_rank_decomposable
     ㉕ 计数型落可分解侧   = 点集结构总有区间分解       —— point_set_decomposable
     ㉖ 可标记的不确定性   = 玩具网络暹界 = 有限+可枚举+守恒 —— uncertainty_is_markable
     ㉗ 可解释性判据       = 网络可解释 ⟺ 层族相干   —— interpretability_criterion
     ㉘ 非线性破相干       = ReLU 不相干 ⟹ 表达力     —— expression_breaks_coherence
     ㉙ 可解释性刻度       = gap ∈ [0,∞]：id 在 0，ReLU 在 ∞ —— interpretability_scale
     ㉚ 黑箱不可修复       = 不相干在复合下保持     —— cnn_gap_persists
     ㉛ 附范畴             = 二值 + 符号 + 自指闭合 —— attached_binary_closed
     ㉜ 附范畴（正名）     = 二值相对于上下文，排中不绝对 —— contextual_binary
     ㉝ 注意力自然导出     = 权重 = 有多少层认为同类   —— attention_from_context
     ㉞ 符号非向量         = 符号 = 对位类 = ℚ        —— symbol_categorical

   统一链：洞（澄明）→ 自我（自己的洞）→ 智能（调节洞）→ 稳定（s/r = n）。

   全程底线：ℚ（不用 ℝ）、无 Classical、零 sorry、构造性、不换根概念。
   ================================================================ -/

/- ================================================================
   归隐理论 · 有限 Grothendieck 链（层 → 环）
   ================================================================

   【五站贯通：site → 预层 → 层 → 几何 → topos】

     ① site（层序）      LayerLadder（Fin m 严格递减）+ ResLayer
     ② 预层（presheaf）  resolution_id / resolution_comp / presheaf_laws
     ③ 层（sheaf）       sheaf_axioms / gluing_general / gluing_condense
     ④ 几何（差异环）     layer_law / sameHueClassTrans_iff_closure
     ⑤ topos（有限初等） terminal_uniq / prodUniversal / sumUniversal /
                         expUniversal / subobject_classifier_finite / piUniversal
        —— Ω = Bool（分辨即分类器），离散图极限 = 守恒网络状态空间

   【与 Grothendieck 的三条结构性分歧（都钉在定理上）】

     site   他的 site 任意复杂   ｜ 你的 site 是有限一维序 Fin m
     预层   他的限制映射可逆     ｜ 你的消解单向（resolution_irreversible）
     sheaf  他的粘合是双向等价   ｜ 你的粘合可行、反粘合必败（半 sheaf）
     几何   他的层绑定拓扑       ｜ 你的层与几何无关，只依赖对称关系

   核心洞见 layer_law：
     任何对称的不可区分关系 r → 传递闭包 → 等价关系 → 商 → 层定律。
     色环（hueDist）和状态空间（commonDist）是同一定理的两个代入——
     **层与几何无关**，这是有限性根的直接后果（没有连续统，就只剩"可不可区分"）。
   ================================================================ -/

/- ================================================================
   归隐理论 · 五层数学（同一种形状，五次重现）
   ================================================================

   差异论不是单一结构。它有五个独立的数学层，每一层都是
   「一个最小数据 + 一条单调/收缩假设 → 一组结论」这一形状：

     ① 层 / 几何层   —— LayerGeometry
          数据：一族对称不可区分关系（按 δ 参数化，单调）
          结论：等价关系 / 单调 / 凝结商 / 粘合 / 层定律
          实例：色环 ringGeometry、状态空间 stateGeometry
          覆盖：theory_layer_coverage

     ② 组合 / 计数层 —— holeSet / holeCount
          数据：一个有限枚举 f : α → β
          结论：秩-零化（洞 = 结构性洞 + 冗余洞）/ 正性（|α| < |β| ⟹ 洞 > 0）
          实例：β = resolveSpace α（差异论的熵）
          覆盖：counting_layer_coverage

     ③ 动力学层     —— ContractingSystem
          数据：一个半步算子 step + 偏差 dev，且 dev(step x) = dev x / 2
          结论：迭代公式 / 严格收缩 / **构造性收敛**（ℚ 的 Archimedes，不用 ℝ 极限）
          实例：reflectSystem（step = reflectStep，dev = deviation）
          覆盖：dynamical_layer_coverage

     ④ 对角线 / 自指层 —— lawvere_fixed_point（一条普适定理，不是结构）
          数据：一个自指枚举（满射）
          结论：不动点存在（Lawvere）/ 对角线洞不可达（Cantor）
          统一：康托尔 / 哥德尔 / 图灵停机 / Russell —— 同一手法
          覆盖：diagonal_hole / self_is_hole / cantor_no_surj

     ⑤ 自指驻留层   —— EgoFixedPoint
          数据：一个自映射 step + 形态（投影幂等 / 对合）+ 该形态的定律
          结论：投影型必有驻留（像即驻留集）/ 对合型由奇偶决定 /
                **有限自映射必有最终周期点**（鸽笼根定理，不动点 = 周期 1）
          实例：egoSelf（自我 = reflect，投影型）、egoTax（税台 = 环反射，对合型）
          统一：EgoFull = kind + dev（驻留 ⟺ 偏差归零；自我 = 投影 + 真实偏差，
                税台 = 对合 + 驻留指示偏差）——fifth_layer_unified
          覆盖：fifth_layer_theorem

   【为什么是五层，不是一层】

     前三层的"数据"互不兼容：层要关系，计数要枚举，动力学要算子。
     第五层把"驻留"从具体系统里抽出来——它不替代任何一层，
     而是指出它们共同的自我指涉面。硬塞进一个结构只会得到空壳定义。
     **理论的分量恰恰在于它有多层**。

   【五层共享同一个源头】

     ① 用 resolveSpace α 定义"不可区分的分辨"；
     ② 用 resolveSpace α 定义"够不着的分辨"；
     ③④⑤ 的自指、洞与驻留也长在同一个 2^n 上。
     一个有限性（n < 2^n），长出五种不同的数学。
   ================================================================ -/

/- ================================================================
   归隐理论 · 洞的七张脸（枢纽）
   ================================================================

   "洞"是唯一横跨全部数学层的对象。七张脸：

     ① 对角线    diag f 永远够不着                     diag_ne_apply
     ② 计数      熵 = 洞数 = 2^n − |像|（余核）         entropy_eq_blindSet_card
     ③ 指标      熵 − 冗余 = 2^n − n（枚举无关）        holeCount_index / entropy_index
     ④ K₀ 群     Quot holeRel ≃ ℤ，洞荷 = 2^n − n       holeGroupEquivInt / holeCharge_int
     ⑤ K₀ 函子   洞荷在不相交并下可加                   holeCharge_sumMap
     ⑥ 结构      堵一个必生一个（不可磨灭）              hole_reborn
     ⑦ 对偶      层封闭（洞数0）vs 自指敞开（洞数>0）    layer_closed_self_open

   最重要的两条：
     · ③ 指标定理：洞的净荷由几何（2^n − n）锁死，观察者（枚举）改不了；
     · ⑦ 对偶：**层 = 凝结的封闭，洞 = 自指的开敞**——这是两种数学的分界线。

   群体洞增（blindSpotBound_add_ge / _add_gt）：
     合并主体后结构性洞 ≥ 各自之和，且（两者都 ≥ 2 时）严格更多——
     指数压过线性，"时间之箭不可回"的计数根据。
   ================================================================ -/

/- ============ 第一层：物理与公理层 ============
   跨维对位（Phase / StateQuant / Interference / commonDist / D）、
   自主排序（toRank / sortAgainst）。
   整个理论的底座，保持顶层命名空间（不包 namespace）。 -/

inductive Phase where
  | positive : Phase   -- 正
  | negative : Phase   -- 负
  | neutral  : Phase   -- 中性
  deriving DecidableEq

structure StateQuant (n : ℕ) where
  val : Fin n → ℚ
  phase : Phase
  deriving DecidableEq

inductive Interference where
  | constructive : Interference  -- 相长
  | destructive  : Interference  -- 相消
  | orthogonal   : Interference  -- 正交
  deriving DecidableEq

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

-- ============ 接轨：相位 = ℚ 的符号，D 的相位规则 = 符号乘法 ============

/-
  【相位不是任选的三值，就是 ℚ 的符号】

  Phase = {正, 负, 中性}，这不是随手设计的三种颜色——
  它就是 ℚ 上的符号 {1, −1, 0}（与 Mathlib 的 SignType 同构）。

  关键：D 的相位合成规则
      正·正 = 相长,  负·负 = 相长,
      正·负 = 相消,  负·正 = 相消,  遇中性得正交
  恰好是**符号乘法**：1·1=1, (−1)·(−1)=1, 1·(−1)=−1, 0·x=0。

  所以"相长 / 相消"不是修辞，是符号相乘：
    · 相长 = 乘积为正（同号：零次或两次半转）；
    · 相消 = 乘积为负（异号：恰好一次半转）。

  于是"半转（−1）"出现在理论最底层：它不是附加概念，
  而是相位代数的基本元素，也是"相消"这个词的全部数学内容。
-/

-- 相位 ↦ 符号（正 1，负 −1，中性 0）。
def phaseSign : Phase → ℤ
  | .positive => 1
  | .negative => -1
  | .neutral => 0

-- 干涉 ↦ 符号（相长 1，相消 −1，正交 0）。
def interferenceSign : Interference → ℤ
  | .constructive => 1
  | .destructive => -1
  | .orthogonal => 0

-- 【核心】D 的相位规则就是符号乘法（距离不出界时）。
theorem D_phase_sign {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ)
    (h : ¬ (commonDist x y > δ)) :
    interferenceSign (D x y δ) = phaseSign x.phase * phaseSign y.phase := by
  simp [D, h]
  cases hx : x.phase <;> cases hy : y.phase <;> decide

-- 【接轨定理】D = 距离门 × 符号乘法。
theorem D_sign {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    interferenceSign (D x y δ)
      = if commonDist x y > δ then 0 else phaseSign x.phase * phaseSign y.phase := by
  by_cases h : commonDist x y > δ
  · simp [D, interferenceSign, h]
  · simp [D, h]
    cases hx : x.phase <;> cases hy : y.phase <;> decide

-- 相消 ⟺ 相位符号之积 = −1 ⟺ 恰好一次半转。
theorem destructive_iff_halfturn {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ)
    (h : commonDist x y ≤ δ) :
    D x y δ = .destructive ↔ phaseSign x.phase * phaseSign y.phase = -1 := by
  simp [D, not_lt.mpr h]
  cases hx : x.phase <;> cases hy : y.phase <;> decide

-- 【三分定理】距离门内，干涉三相 ⟺ 符号乘积三值 {+1, −1, 0}。
theorem D_trichotomy {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ)
    (h : commonDist x y ≤ δ) :
    (D x y δ = .constructive ↔ phaseSign x.phase * phaseSign y.phase = 1) ∧
    (D x y δ = .destructive ↔ phaseSign x.phase * phaseSign y.phase = -1) ∧
    (D x y δ = .orthogonal ↔ phaseSign x.phase * phaseSign y.phase = 0) := by
  simp [D, not_lt.mpr h]
  cases hx : x.phase <;> cases hy : y.phase <;> decide

-- 相位 ↦ 符号是单射：三值相位就是三个符号，没有多余自由度。
theorem phaseSign_injective : Function.Injective phaseSign := by
  intro a b h
  cases a <;> cases b <;> simp [phaseSign] at h ⊢

-- 等级序就是"1 − 符号"：相长(0) < 正交(1) < 相消(2) 全部由符号给出。
theorem toRank_eq_one_sub_sign (i : Interference) :
    (i.toRank : ℤ) = 1 - interferenceSign i := by
  cases i <;> decide

-- 两次半转回到原地：(−1)·(−1) = 1 —— 相消相位自乘即相长。
theorem halfturn_sq : phaseSign .negative * phaseSign .negative = (1 : ℤ) := by
  decide

-- ============ 接轨 2：相位 ≅ Mathlib 的符号类型 SignType ============

/-
  Phase 与 Mathlib 的 SignType = {−1, 0, 1} 是**结构同构**，不只是取值相同。
  SignType 自带 CommGroupWithZero、LinearOrder、Fintype——
  相位一旦等同它，就免费继承乘法、次序、有限性。

  于是「相消 = 乘 −1（半转）」不再是定义出来的巧合：
  它成为 Mathlib 代数（SignType 的乘法）在这个接口上的一个实例。
-/

def phaseToSignType : Phase → SignType
  | .positive => 1
  | .negative => -1
  | .neutral  => 0

def signTypeToPhase : SignType → Phase
  | 1 => .positive
  | -1 => .negative
  | 0 => .neutral

theorem phaseToSignType_leftInverse (s : SignType) :
    phaseToSignType (signTypeToPhase s) = s := by
  cases s <;> rfl

theorem phaseToSignType_rightInverse (p : Phase) :
    signTypeToPhase (phaseToSignType p) = p := by
  cases p <;> rfl

-- 相位 ≃ 符号（构造性同构）。
def phaseEquivSignType : Phase ≃ SignType where
  toFun := phaseToSignType
  invFun := signTypeToPhase
  left_inv := phaseToSignType_rightInverse
  right_inv := phaseToSignType_leftInverse

-- 同构与已有 phaseSign 相容：phaseSign = 转入 SignType 再 cast 到 ℤ。
theorem phaseSign_eq_signTypeCast (p : Phase) :
    phaseSign p = (phaseToSignType p : ℤ) := by
  cases p <;> rfl

def interferenceToSignType : Interference → SignType
  | .constructive => 1
  | .destructive => -1
  | .orthogonal => 0

theorem interferenceSign_eq_signTypeCast (i : Interference) :
    interferenceSign i = (interferenceToSignType i : ℤ) := by
  cases i <;> rfl

-- 【主定理】D 的相位规则 = SignType 乘法（距离门内）。
theorem D_signType {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ)
    (h : commonDist x y ≤ δ) :
    interferenceToSignType (D x y δ)
      = phaseToSignType x.phase * phaseToSignType y.phase := by
  simp [D, not_lt.mpr h]
  cases hx : x.phase <;> cases hy : y.phase <;> decide

-- 相位只有三值：同构直接搬来 Fintype 与基数 3（构造性，不碰 Classical）。
instance : Fintype Phase := Fintype.ofEquiv SignType phaseEquivSignType.symm

theorem phase_card : Fintype.card Phase = 3 := by
  rw [Fintype.card_congr phaseEquivSignType]
  rw [Fintype.card_congr SignType.fin3Equiv.toEquiv]
  exact Fintype.card_fin 3

-- 正交（中性）是乘法吸收元：一旦正交，任何相位相乘仍为正交。
theorem orthogonal_absorbs (s : SignType) :
    interferenceToSignType .orthogonal * s = 0 := by
  simp [interferenceToSignType]

-- 半转在 SignType 里是二阶元：neg · neg = 1。
theorem signType_halfturn :
    phaseToSignType .negative * phaseToSignType .negative = (1 : SignType) := by
  decide

-- ============ 体量与字典序 ============

-- 范数平方（L2 平方和，衡量“体量/生命力”）
def normSq {n : ℕ} (x : StateQuant n) : ℚ :=
  ∑ i : Fin n, (x.val i) ^ 2

-- 范数平方非负（体量恒非负）
theorem normSq_nonneg {n : ℕ} (x : StateQuant n) : 0 ≤ normSq x := by
  unfold normSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x.val i))

-- 字典序：先比干涉等级 rank，rank 相同比体量（体量越大越优先）
def lexLe {m n : ℕ} (ref : StateQuant n) (δ : ℚ) (x y : StateQuant m) : Prop :=
  (D x ref δ).toRank < (D y ref δ).toRank ∨
  ((D x ref δ).toRank = (D y ref δ).toRank ∧ normSq x ≥ normSq y)

-- lexLe 传递（rank 用 <，normSq 用 ≥，字典序传递）
instance lexLe_trans {m n : ℕ} (ref : StateQuant n) (δ : ℚ) : IsTrans (StateQuant m) (lexLe (m := m) ref δ) := by
  constructor
  intro x y z hxy hyz
  unfold lexLe at hxy hyz ⊢
  rcases hxy with hxy | hxy
  · rcases hyz with hyz | hyz
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl (lt_of_lt_of_le hxy (le_of_eq hyz.1))
  · rcases hxy with ⟨rxy, mxy⟩
    rcases hyz with hyz | hyz
    · exact Or.inl (lt_of_le_of_lt (le_of_eq rxy) hyz)
    · rcases hyz with ⟨ryz, myz⟩
      exact Or.inr ⟨rxy.trans ryz, le_trans myz mxy⟩

-- lexLe 全序（rank 三分 + normSq 全序）
instance lexLe_total {m n : ℕ} (ref : StateQuant n) (δ : ℚ) : Std.Total (lexLe (m := m) ref δ) := by
  constructor
  intro x y
  unfold lexLe
  by_cases hlt : (D x ref δ).toRank < (D y ref δ).toRank
  · exact Or.inl (Or.inl hlt)
  · by_cases hgt : (D y ref δ).toRank < (D x ref δ).toRank
    · exact Or.inr (Or.inl hgt)
    · have h_eq : (D x ref δ).toRank = (D y ref δ).toRank := by omega
      by_cases hm : normSq y ≤ normSq x
      · exact Or.inl (Or.inr ⟨h_eq, hm⟩)
      · exact Or.inr (Or.inr ⟨h_eq.symm, le_of_lt (lt_of_not_ge hm)⟩)

-- lexLe 可判定（rank 用 ℕ 的 <，normSq 用 ℚ 的 ≥，均 decidable）
instance lexLe_decidable {m n : ℕ} (ref : StateQuant n) (δ : ℚ) : DecidableRel (lexLe (m := m) ref δ) := by
  intro x y
  unfold lexLe
  infer_instance

-- lexLe 自反（rank x = rank x ∧ normSq x ≥ normSq x）
instance lexLe_refl {m n : ℕ} (ref : StateQuant n) (δ : ℚ) : Std.Refl (lexLe (m := m) ref δ) := by
  constructor
  intro x
  unfold lexLe
  right
  exact ⟨rfl, le_rfl⟩

-- 按与参考点的对位结果排序：先比干涉等级，等级相同比体量（体量大者优先）（跨维，支持 m ≠ n）
def sortAgainst {m n : ℕ} (ref : StateQuant n) (candidates : List (StateQuant m)) (δ : ℚ) : List (StateQuant m) :=
  List.insertionSort (lexLe (m := m) ref δ) candidates

-- 定理：排序后的列表，字典序（rank，体量）非递减（Pairwise）
set_option linter.style.haveILetI false in
theorem sortAgainst_sorted {m n : ℕ} (ref : StateQuant n) (candidates : List (StateQuant m)) (δ : ℚ) :
    List.Pairwise (lexLe (m := m) ref δ) (sortAgainst ref candidates δ) := by
  let r := lexLe (m := m) ref δ
  haveI : Std.Total r := lexLe_total ref δ
  haveI : IsTrans (StateQuant m) r := lexLe_trans ref δ
  simpa [sortAgainst, r] using (List.pairwise_insertionSort r candidates)

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
/- ============ 第二层：自我与演化层 ============
   MemoryLibrary / awaken / awaken_optimal / step / evolve / IsSelf / I_am_I。
   这一层通过 Ego 命名空间引用第一层的底座。 -/
namespace Ego

/- ═══════════════════════════════════════════════════════════════════
   【自我稳定性判据】—— Ego 层三定理闭环（字典序：rank 优先，体量 tie-break）
   
   核心结论：自我稳定 ⟺ 排他性 ∨（位置优势 ∧ 体量支配）
   
   字典序 lexLe：先比干涉等级 rank，rank 相同比体量 normSq（体量大者优先）。
   “排最前” = rank 最小 ∧（同 rank 中）体量最大。
   
   四条定理：
   · I_am_always_I          有排他性（rank 唯一 0）→ 绝对稳定
   · old_ego_no_replacement 无排他性但占头部且体量支配 → 仍稳定
   · ego_replacement        无排他性且头部被占且体量被超越 → 被夺舍
   · solid_ego_immunity     无排他性但体量更大 → 免疫夺舍
   
   守护自我 = 绝对排他 + 头部先发 + 体量支配。
   ═══════════════════════════════════════════════════════════════════ -/

-- ============ 记忆库与唤醒机制 ============

abbrev MemoryLibrary (n : ℕ) := List (StateQuant n)

def awaken {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) : Option (StateQuant m) :=
  match sortAgainst ref lib δ with
  | [] => none
  | best :: _ => some best

-- 唤醒最优性：best 在字典序下 ≤ 库里任何元素
set_option linter.style.haveILetI false in
theorem awaken_optimal {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) 
    (best : StateQuant m) (h_awaken : awaken lib ref δ = some best) :
    ∀ (x : StateQuant m), x ∈ lib → lexLe (m := m) ref δ best x := by
  intro x hx
  unfold awaken at h_awaken
  cases hsort : sortAgainst ref lib δ with
  | nil => simp [hsort] at h_awaken
  | cons b rest =>
      simp [hsort] at h_awaken
      have hbest : b = best := h_awaken
      have hpair : List.Pairwise (lexLe (m := m) ref δ) (sortAgainst ref lib δ) :=
        sortAgainst_sorted ref lib δ
      rw [hsort] at hpair
      have hperm : List.Perm (sortAgainst ref lib δ) lib := by
        simpa [sortAgainst] using (List.perm_insertionSort (lexLe (m := m) ref δ) lib)
      have hx' : x ∈ sortAgainst ref lib δ := (List.Perm.mem_iff hperm).mpr hx
      rw [hsort] at hx'
      haveI : Std.Refl (lexLe (m := m) ref δ) := lexLe_refl ref δ
      haveI : Inhabited (StateQuant m) := ⟨⟨fun _ => 0, Phase.neutral⟩⟩
      have hrel : lexLe (m := m) ref δ b x :=
        List.Pairwise.head!_le hpair hx'
      simpa [hbest] using hrel

-- ============ 元序列演化与动力学 ============

def step {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (_δ : ℚ) : MemoryLibrary n :=
  ref :: lib

def evolve {n : ℕ} (init_lib : MemoryLibrary n) (inputs : ℕ → StateQuant n) (δ : ℚ) : ℕ → MemoryLibrary n
  | 0 => init_lib
  | t + 1 => step (evolve init_lib inputs δ t) (inputs t) δ

-- ============ 自我确认不动点定理（Ego Fixed-Point） ============

def IsSelf {n : ℕ} (ref : StateQuant n) (δ : ℚ) : Prop :=
  D ref ref δ = Interference.constructive

-- 辅助引理：ref rank 0 且支配 x（同 rank 时体量更大）⟹ lexLe ref x
lemma lexLe_self_dom {n : ℕ} (ref : StateQuant n) (δ : ℚ) (x : StateQuant n)
    (h_rank_ref : (D ref ref δ).toRank = 0)
    (h_dom : (D x ref δ).toRank = 0 → normSq ref ≥ normSq x) :
    lexLe (m := n) ref δ ref x := by
  unfold lexLe
  by_cases h : (D x ref δ).toRank = 0
  · right
    exact ⟨h_rank_ref.trans h.symm, h_dom h⟩
  · left
    simpa [h_rank_ref] using (Nat.pos_iff_ne_zero.mpr h)

-- 关键引理 1：ref rank 0 且支配 l，排头部，排序后仍在头部
-- （提到 I_am_I 之前，供所有"自我不动点"定理复用——原先各定理都内联了这段证明。）
lemma sortAgainst_head_cons {n : ℕ} (ref : StateQuant n) (δ : ℚ) (l : MemoryLibrary n)
    (h_rank0 : (D ref ref δ).toRank = 0)
    (h_dom : ∀ x ∈ l, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x) :
    sortAgainst ref (ref :: l) δ = ref :: sortAgainst ref l δ := by
  have hrel : ∀ b ∈ l, lexLe (m := n) ref δ ref b := by
    intro b hb
    exact lexLe_self_dom ref δ b h_rank0 (h_dom b hb)
  unfold sortAgainst
  exact List.insertionSort_cons_of_forall_rel (lexLe (m := n) ref δ) hrel

-- 自我确认不动点：ref 自反相长且支配同阶（rank 0 中体量最大），唤醒自己还是自己
theorem I_am_I {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x) :
    awaken (step lib ref δ) ref δ = some ref := by
  unfold IsSelf at h_self
  have h_rank0 : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  have hcons : sortAgainst ref (ref :: lib) δ = ref :: sortAgainst ref lib δ :=
    sortAgainst_head_cons ref δ lib h_rank0 h_dom
  unfold awaken
  simp only [step]
  rw [hcons]

-- ============ 全局时间演化下的自我不动点（Temporal Fixed-Point） ============

-- ============ 头部保持的唯一核心：a 不支配 head ⟹ head 保持 ============

-- 最宽的签名：只要 a 不支配 head，插入 a 后 head 仍在头部。
-- sortAgainst_head_preserved / _gen / head_preserved_general 三者都只是
-- "¬ lexLe a head" 的三种不同推导方式。
lemma sortAgainst_head_preserved_notle {n : ℕ} (ref head a : StateQuant n) (δ : ℚ) (l : MemoryLibrary n)
    (h_notle : ¬ lexLe (m := n) ref δ a head)
    (h_head : ∃ rest, sortAgainst ref l δ = head :: rest) :
    ∃ rest', sortAgainst ref (a :: l) δ = head :: rest' := by
  rcases h_head with ⟨rest, hrest⟩
  have hrest' : List.insertionSort (lexLe (m := n) ref δ) l = head :: rest := by
    simpa [sortAgainst] using hrest
  unfold sortAgainst
  rw [List.insertionSort_cons]
  rw [hrest']
  rw [List.orderedInsert_of_not_le (lexLe (m := n) ref δ) rest h_notle]
  exact ⟨List.orderedInsert (lexLe (m := n) ref δ) a rest, rfl⟩

-- 关键引理 2：ref 排序后已在头部，新元素 a（rank > 0）插入后 ref 仍在头部
lemma sortAgainst_head_preserved {n : ℕ} (ref : StateQuant n) (δ : ℚ) (a : StateQuant n) (l : MemoryLibrary n)
    (h_rank0 : (D ref ref δ).toRank = 0)
    (ha_gt : (D a ref δ).toRank > 0)
    (h_head : ∃ rest, sortAgainst ref l δ = ref :: rest) :
    ∃ rest', sortAgainst ref (a :: l) δ = ref :: rest' :=
  sortAgainst_head_preserved_notle ref ref a δ l
    (by
      unfold lexLe
      rintro (hlt | ⟨heq, _⟩)
      · exact (not_lt_of_gt (by simpa [h_rank0] using ha_gt)) hlt
      · exact (ne_of_gt (by simpa [h_rank0] using ha_gt)) heq)
    h_head

-- 关键引理 3（通用保持）：a 若 rank 0 则体量严格小于 ref，则 ref 保持头部。
-- 这一条同时覆盖"rank > 0 的输入"和"rank 0 但体量更小的输入"——
-- solid_ego_immunity / temporal_solid_immunity / core_memory_persists(_relaxed) 都复用它。
lemma head_preserved_general {n : ℕ} (ref : StateQuant n) (δ : ℚ) (a : StateQuant n) (l : MemoryLibrary n)
    (h_rank_ref : (D ref ref δ).toRank = 0)
    (h_a : (D a ref δ).toRank = 0 → normSq ref > normSq a)
    (h_head : ∃ rest, sortAgainst ref l δ = ref :: rest) :
    ∃ rest', sortAgainst ref (a :: l) δ = ref :: rest' :=
  sortAgainst_head_preserved_notle ref ref a δ l
    (by
      unfold lexLe
      rintro (hlt | ⟨heq, hm⟩)
      · have : (D a ref δ).toRank < 0 := by
          rw [h_rank_ref] at hlt
          exact hlt
        exact Nat.not_lt_zero _ this
      · exact (not_le_of_gt (h_a (heq.trans h_rank_ref))) hm)
    h_head

-- 主定理：全局时间演化下的自我不动点
-- 关键引理 4（迭代保持）：每一步输入都"若同阶则体量严格小于 ref"，则 ref 恒居头部。
-- 统一覆盖 I_am_always_I（rank>0 输入）、head_before_t、temporal_solid_immunity。
lemma head_iter {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_rank_ref : (D ref ref δ).toRank = 0)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x) :
    ∀ t, (∀ k < t, (D (inputs k) ref δ).toRank = 0 → normSq ref > normSq (inputs k)) →
      ∃ rest, sortAgainst ref (evolve (ref :: lib) inputs δ t) δ = ref :: rest := by
  intro t
  induction t with
  | zero =>
      intro _
      exact ⟨sortAgainst ref lib δ, by simpa [evolve] using (sortAgainst_head_cons ref δ lib h_rank_ref h_dom_lib)⟩
  | succ k ih =>
      intro hk
      have ih' := ih (fun m hm => hk m (Nat.lt_trans hm (Nat.lt_succ_self k)))
      have hstep := head_preserved_general ref δ (inputs k) (evolve (ref :: lib) inputs δ k)
        h_rank_ref (hk k (Nat.lt_succ_self k)) ih'
      simpa [evolve, step] using hstep

theorem I_am_always_I {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs : ∀ t, (D (inputs t) ref δ).toRank > 0)
    (t : ℕ) :
    awaken (evolve (ref :: lib) inputs δ t) ref δ = some ref := by
  unfold IsSelf at h_self
  have h_rank0 : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  rcases head_iter lib ref δ inputs h_rank0 h_dom t
    (fun k _ h0 => by have hgt := h_inputs k; omega) with ⟨rest, hrest⟩
  unfold awaken
  rw [hrest]

-- ============ 自我同化/夺舍定理（Ego Replacement Theorem） ============

-- 当出现同等相长（rank 0）且体量更大的替代者时，自我被夺舍
lemma ego_replacement {n : ℕ} (lib : MemoryLibrary n) (ref a : StateQuant n) (δ : ℚ)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_a : (D a ref δ).toRank = 0)
    (h_mass : normSq a ≥ normSq ref)
    (_h_ne : a ≠ ref) :
    awaken (a :: ref :: lib) ref δ = some a := by
  unfold IsSelf at h_self
  have h_rank_ref : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  have h_head : sortAgainst ref (a :: ref :: lib) δ = a :: ref :: sortAgainst ref lib δ := by
    unfold sortAgainst
    rw [List.insertionSort_cons]
    have hcons : List.insertionSort (lexLe (m := n) ref δ) (ref :: lib) =
        ref :: List.insertionSort (lexLe (m := n) ref δ) lib := by
      simpa [sortAgainst] using (sortAgainst_head_cons ref δ lib h_rank_ref h_dom)
    rw [hcons]
    have ha_le : lexLe (m := n) ref δ a ref := by
      unfold lexLe
      right
      exact ⟨h_a.trans h_rank_ref.symm, h_mass⟩
    exact List.orderedInsert_cons_of_le (lexLe (m := n) ref δ) (List.insertionSort (lexLe (m := n) ref δ) lib) ha_le
  unfold awaken
  rw [h_head]

-- 旧并列者不夺舍：同等相长但体量更小的 a 排在 ref 后面，无法越过 ref
lemma old_ego_no_replacement {n : ℕ} (lib : MemoryLibrary n) (ref a : StateQuant n) (δ : ℚ)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_a : (D a ref δ).toRank = 0)
    (h_mass_ref : normSq ref ≥ normSq a) :
    awaken (ref :: a :: lib) ref δ = some ref := by
  unfold IsSelf at h_self
  have h_rank_ref : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  have h_dom_a : ∀ x ∈ a :: lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x := by
    intro x hx hx0
    rcases List.mem_cons.mp hx with hxa | hxl
    · subst hxa
      exact h_mass_ref
    · exact h_dom x hxl hx0
  have h_head : sortAgainst ref (ref :: a :: lib) δ = ref :: sortAgainst ref (a :: lib) δ :=
    sortAgainst_head_cons ref δ (a :: lib) h_rank_ref h_dom_a
  unfold awaken
  rw [h_head]

-- 实体自我的绝对防御：同等相长但体量更小的 a 排在前面，也无法夺舍（体量大者免疫）
theorem solid_ego_immunity {n : ℕ} (lib : MemoryLibrary n) (ref a : StateQuant n) (δ : ℚ)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (_h_a_rank0 : (D a ref δ).toRank = 0)
    (h_mass : normSq a < normSq ref) :
    awaken (a :: ref :: lib) ref δ = some ref := by
  unfold IsSelf at h_self
  have h_rank_ref : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  -- ref 在 (ref :: lib) 中居头部
  have h_head0 : ∃ rest, sortAgainst ref (ref :: lib) δ = ref :: rest :=
    ⟨_, sortAgainst_head_cons ref δ lib h_rank_ref h_dom⟩
  -- a 若 rank 0 则体量严格小于 ref ⟹ 通用保持引理直接给出结论
  have h_a : (D a ref δ).toRank = 0 → normSq ref > normSq a := fun _ => h_mass
  rcases head_preserved_general ref δ a (ref :: lib) h_rank_ref h_a h_head0 with ⟨rest', hrest'⟩
  unfold awaken
  rw [hrest']


-- ============ 时间演化下的夺舍（Temporal Ego Replacement） ============

-- 辅助引理：若历史输入（k < t）rank 都 > 0，则 ref 在 t 时刻稳居头部
lemma head_before_t {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_rank_ref : (D ref ref δ).toRank = 0)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x) :
    ∀ t, (∀ k < t, (D (inputs k) ref δ).toRank > 0) →
      ∃ rest, sortAgainst ref (evolve (ref :: lib) inputs δ t) δ = ref :: rest := by
  intro t hk
  exact head_iter lib ref δ inputs h_rank_ref h_dom_lib t
    (fun k hkt h0 => by have hgt := hk k hkt; omega)

-- 若 t 时刻出现 rank 0 且体量 ≥ ref 的输入，则从 t+1 起系统唤醒的是该输入
theorem temporal_ego_replacement {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (t : ℕ)
    (h_self : IsSelf ref δ)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_before : ∀ k < t, (D (inputs k) ref δ).toRank > 0)
    (h_input_t_rank0 : (D (inputs t) ref δ).toRank = 0)
    (h_input_t_mass : normSq (inputs t) ≥ normSq ref) :
    awaken (evolve (ref :: lib) inputs δ (t + 1)) ref δ = some (inputs t) := by
  unfold IsSelf at h_self
  have h_rank_ref : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  -- 第一步：t 时刻之前 ref 稳居头部
  have h_head_t : ∃ rest, sortAgainst ref (evolve (ref :: lib) inputs δ t) δ = ref :: rest :=
    head_before_t lib ref δ inputs h_rank_ref h_dom_lib t h_inputs_before
  -- 第二步：inputs t 插入，rank 0 且体量 ≥ ref，替换 ref 成为头部
  rcases h_head_t with ⟨rest, hrest⟩
  have h_head_succ : sortAgainst ref (evolve (ref :: lib) inputs δ (t + 1)) δ = inputs t :: ref :: rest := by
    unfold sortAgainst
    simp only [evolve, step]
    rw [List.insertionSort_cons]
    have hsort_t : List.insertionSort (lexLe (m := n) ref δ) (evolve (ref :: lib) inputs δ t) = ref :: rest := by
      simpa [sortAgainst] using hrest
    rw [hsort_t]
    have h_le : lexLe (m := n) ref δ (inputs t) ref := by
      unfold lexLe
      right
      exact ⟨h_input_t_rank0.trans h_rank_ref.symm, h_input_t_mass⟩
    rw [List.orderedInsert_cons_of_le (lexLe (m := n) ref δ) rest h_le]
  -- 第三步：awaken 唤醒 inputs t
  unfold awaken
  rw [h_head_succ]


-- ============ 时间演化下的体量免疫（Temporal Solid Immunity） ============

-- 时间演化下的体量免疫：任何同阶输入的体量都严格小于 ref，则 ref 恒稳居头部
theorem temporal_solid_immunity {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_mass : ∀ t, (D (inputs t) ref δ).toRank = 0 → normSq ref > normSq (inputs t))
    (t : ℕ) :
    awaken (evolve (ref :: lib) inputs δ t) ref δ = some ref := by
  unfold IsSelf at h_self
  have h_rank_ref : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  rcases head_iter lib ref δ inputs h_rank_ref h_dom_lib t
    (fun k _ h0 => h_inputs_mass k h0) with ⟨rest, hrest⟩
  unfold awaken
  rw [hrest]

-- ============ D6 消解算子（遗忘与粗化） ============

-- 消解（粗化）：滤除体量小于 min_mass 的记忆，模拟随时间衰减后被遗忘。
def dissolve {n : ℕ} (lib : MemoryLibrary n) (min_mass : ℚ) : MemoryLibrary n :=
  lib.filter (fun x => min_mass ≤ normSq x)

-- 时间演化 + 消解（D6）：每步吸收新输入后，执行一次消解。
def evolve_with_dissolve {n : ℕ} (init_lib : MemoryLibrary n) (inputs : ℕ → StateQuant n)
    (δ min_mass : ℚ) : ℕ → MemoryLibrary n
  | 0 => init_lib
  | t + 1 =>
      let new_lib := step (evolve_with_dissolve init_lib inputs δ min_mass t) (inputs t) δ
      dissolve new_lib min_mass

-- 辅助引理：若 a 不支配 ref，则从 a :: l 的排序中去掉 a，ref 仍保持头部。
lemma sortAgainst_erase_head {n : ℕ} (ref : StateQuant n) (δ : ℚ) (a : StateQuant n) (l : MemoryLibrary n)
    (h_head : ∃ rest, sortAgainst ref (a :: l) δ = ref :: rest)
    (h_not_dom : ¬ lexLe (m := n) ref δ a ref) :
    ∃ rest', sortAgainst ref l δ = ref :: rest' := by
  rcases h_head with ⟨rest, hrest⟩
  unfold sortAgainst at hrest
  rw [List.insertionSort_cons] at hrest
  cases hL : List.insertionSort (lexLe (m := n) ref δ) l with
  | nil =>
      simp [hL] at hrest
      have ha_ref : a = ref := hrest.1
      subst ha_ref
      exact False.elim (h_not_dom (by unfold lexLe; right; exact ⟨rfl, le_rfl⟩))
  | cons b L' =>
      rw [hL] at hrest
      rw [List.orderedInsert_cons] at hrest
      by_cases hab : lexLe (m := n) ref δ a b
      · simp [hab] at hrest
        have ha_ref : a = ref := hrest.1
        subst ha_ref
        exact False.elim (h_not_dom (by unfold lexLe; right; exact ⟨rfl, le_rfl⟩))
      · simp [hab] at hrest
        have hb_ref : b = ref := hrest.1
        subst hb_ref
        refine ⟨L', ?_⟩
        simpa [sortAgainst] using hL

-- 辅助引理：若 a 支配 ref 且 ref 是 (a :: l) 排序后的头部，则 a = ref。
lemma sortAgainst_head_eq_ref_of_dom {n : ℕ} (ref : StateQuant n) (δ : ℚ) (a : StateQuant n)
    (l rest : MemoryLibrary n)
    (h_head : sortAgainst ref (a :: l) δ = ref :: rest)
    (h_dom : lexLe (m := n) ref δ a ref) :
    a = ref := by
  unfold sortAgainst at h_head
  rw [List.insertionSort_cons] at h_head
  cases hL : List.insertionSort (lexLe (m := n) ref δ) l with
  | nil =>
      simp [hL] at h_head
      exact h_head.1
  | cons b L' =>
      rw [hL] at h_head
      rw [List.orderedInsert_cons] at h_head
      by_cases hab : lexLe (m := n) ref δ a b
      · simp [hab] at h_head
        exact h_head.1
      · simp [hab] at h_head
        have hb_ref : b = ref := h_head.1
        subst hb_ref
        exact False.elim (hab h_dom)

-- 消解保持头部：ref 排序后居头部且不被消解（normSq ≥ min_mass），消解后 ref 仍居头部。
lemma dissolve_head_preserved {n : ℕ} (ref : StateQuant n) (δ min_mass : ℚ) (l : MemoryLibrary n)
    (h_rank_ref : (D ref ref δ).toRank = 0)
    (h_dom : ∀ x ∈ l, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_head : ∃ rest, sortAgainst ref l δ = ref :: rest)
    (h_solid : normSq ref ≥ min_mass) :
    ∃ rest', sortAgainst ref (dissolve l min_mass) δ = ref :: rest' := by
  induction l with
  | nil => rcases h_head with ⟨rest, hrest⟩; simp [sortAgainst] at hrest
  | cons x xs ih =>
      rcases h_head with ⟨rest, hrest⟩
      by_cases hpx : min_mass ≤ normSq x
      · -- x 保留
        by_cases hx_le : lexLe (m := n) ref δ x ref
        · -- x 支配 ref ⟹ x = ref
          have hx_eq_ref : x = ref := sortAgainst_head_eq_ref_of_dom ref δ x xs rest hrest hx_le
          subst x
          have h_dom_filter : ∀ y ∈ dissolve xs min_mass, (D y ref δ).toRank = 0 → normSq ref ≥ normSq y := by
            intro y hy h0
            exact h_dom y (List.mem_cons_of_mem ref (List.mem_of_mem_filter hy)) h0
          have hcons := sortAgainst_head_cons ref δ (dissolve xs min_mass) h_rank_ref h_dom_filter
          refine ⟨sortAgainst ref (dissolve xs min_mass) δ, ?_⟩
          simpa [dissolve, h_solid] using hcons
        · -- x 不支配 ref
          have h_dom_xs : ∀ y ∈ xs, (D y ref δ).toRank = 0 → normSq ref ≥ normSq y := by
            intro y hy h0
            exact h_dom y (List.mem_cons_of_mem x hy) h0
          rcases sortAgainst_erase_head ref δ x xs ⟨rest, hrest⟩ hx_le with ⟨rest', hrest'⟩
          rcases ih h_dom_xs ⟨rest', hrest'⟩ with ⟨rest'', hrest''⟩
          have hx_mass : (D x ref δ).toRank = 0 → normSq ref > normSq x := by
            intro h0
            have hnot_le : ¬ (normSq ref ≤ normSq x) := by
              intro hle
              apply hx_le
              unfold lexLe
              right
              exact ⟨h0.trans h_rank_ref.symm, hle⟩
            exact lt_of_not_ge hnot_le
          simpa [dissolve, hpx] using (head_preserved_general ref δ x (dissolve xs min_mass) h_rank_ref hx_mass ⟨rest'', hrest''⟩)
      · -- x 被过滤
        have hx_not_dom : ¬ lexLe (m := n) ref δ x ref := by
          unfold lexLe
          rintro (hlt | ⟨heq, hm⟩)
          · omega
          · have hx_lt : normSq x < min_mass := lt_of_not_ge hpx
            have hx_lt_ref : normSq x < normSq ref := lt_of_lt_of_le hx_lt h_solid
            exact (not_lt_of_ge hm) hx_lt_ref
        have h_dom_xs : ∀ y ∈ xs, (D y ref δ).toRank = 0 → normSq ref ≥ normSq y := by
          intro y hy h0
          exact h_dom y (List.mem_cons_of_mem x hy) h0
        rcases sortAgainst_erase_head ref δ x xs ⟨rest, hrest⟩ hx_not_dom with ⟨rest', hrest'⟩
        simpa [dissolve, hpx] using (ih h_dom_xs ⟨rest', hrest'⟩)

-- ============ 核心记忆生存（通用版）：一个定理覆盖两种输入 ============

/-
  【核心记忆的绝对生存（D6 的威力）】

  ref 自反（rank 0）、支配初始库、体量 ≥ min_mass（不被消解），
  且每个输入"若同阶则体量严格小于 ref"，则无论多少时间步、多少次消解，
  awaken 出来的始终是 ref。

  关键：输入条件统一成一句
    (D (inputs t) ref δ).toRank = 0 → normSq ref > normSq (inputs t)
  它同时覆盖两种情形：
    · 输入 rank 恒 > 0（前件恒假）——core_memory_persists
    · 输入同阶但体量 < min_mass ≤ normSq ref（被 dissolve 滤掉）——core_memory_persists_relaxed
  原先这两个定理各写一遍相同的归纳，现在归纳只写一次。
-/
theorem core_memory_persists_general {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ min_mass : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs : ∀ t, (D (inputs t) ref δ).toRank = 0 → normSq ref > normSq (inputs t))
    (h_solid : normSq ref ≥ min_mass) :
    ∀ t, awaken (evolve_with_dissolve (ref :: lib) inputs δ min_mass t) ref δ = some ref := by
  unfold IsSelf at h_self
  have h_rank_ref : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  -- 联合归纳不变量：ref 头部 + ref 支配
  have h_inv : ∀ s, (∃ rest, sortAgainst ref (evolve_with_dissolve (ref :: lib) inputs δ min_mass s) δ = ref :: rest) ∧
      (∀ x ∈ evolve_with_dissolve (ref :: lib) inputs δ min_mass s, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x) := by
    intro s
    induction s with
    | zero =>
        constructor
        · exact ⟨sortAgainst ref lib δ, by simpa [evolve_with_dissolve] using (sortAgainst_head_cons ref δ lib h_rank_ref h_dom)⟩
        · intro x hx h0
          rcases List.mem_cons.mp hx with hxr | hxl
          · subst hxr
            exact le_rfl
          · exact h_dom x hxl h0
    | succ k ih =>
        rcases ih with ⟨hhead, hdom⟩
        rcases hhead with ⟨rest, hrest⟩
        have h_head_input : ∃ rest', sortAgainst ref (inputs k :: evolve_with_dissolve (ref :: lib) inputs δ min_mass k) δ = ref :: rest' :=
          head_preserved_general ref δ (inputs k) (evolve_with_dissolve (ref :: lib) inputs δ min_mass k) h_rank_ref (h_inputs k) ⟨rest, hrest⟩
        have h_dom_input : ∀ x ∈ inputs k :: evolve_with_dissolve (ref :: lib) inputs δ min_mass k, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x := by
          intro x hx h0
          rcases List.mem_cons.mp hx with hxi | hxl
          · subst hxi
            exact le_of_lt (h_inputs k h0)
          · exact hdom x hxl h0
        have h_head_dissolve : ∃ rest', sortAgainst ref (dissolve (inputs k :: evolve_with_dissolve (ref :: lib) inputs δ min_mass k) min_mass) δ = ref :: rest' :=
          dissolve_head_preserved ref δ min_mass (inputs k :: evolve_with_dissolve (ref :: lib) inputs δ min_mass k) h_rank_ref h_dom_input h_head_input h_solid
        have h_dom_dissolve : ∀ x ∈ dissolve (inputs k :: evolve_with_dissolve (ref :: lib) inputs δ min_mass k) min_mass, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x := by
          intro x hx h0
          exact h_dom_input x (List.mem_of_mem_filter hx) h0
        constructor
        · simpa [evolve_with_dissolve, step] using h_head_dissolve
        · simpa [evolve_with_dissolve, step] using h_dom_dissolve
  intro t
  rcases (h_inv t).1 with ⟨rest, hrest⟩
  unfold awaken
  rw [hrest]

-- 核心记忆的绝对生存（输入 rank 恒 > 0）：通用版的特例（前件恒假）。
theorem core_memory_persists {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ min_mass : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs : ∀ t, (D (inputs t) ref δ).toRank > 0)
    (h_solid : normSq ref ≥ min_mass) :
    ∀ t, awaken (evolve_with_dissolve (ref :: lib) inputs δ min_mass t) ref δ = some ref :=
  core_memory_persists_general lib ref δ min_mass inputs h_self h_dom
    (fun t h0 => by have hgt := h_inputs t; omega) h_solid

-- 核心记忆的绝对生存（放宽版 / D6 发挥威力）：同阶但体量 < min_mass 的"微小创伤"输入
-- 体量不够，排不到 ref 前面，又被 dissolve 滤出记忆库——ref 永远是王。
theorem core_memory_persists_relaxed {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ min_mass : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_relaxed : ∀ t, (D (inputs t) ref δ).toRank = 0 → normSq (inputs t) < min_mass)
    (h_solid : normSq ref ≥ min_mass) :
    ∀ t, awaken (evolve_with_dissolve (ref :: lib) inputs δ min_mass t) ref δ = some ref :=
  core_memory_persists_general lib ref δ min_mass inputs h_self h_dom
    (fun t h0 => lt_of_lt_of_le (h_inputs_relaxed t h0) h_solid) h_solid

-- 同维面积平方（Gram 行列式）
def areaSq {n : ℕ} (x y : StateQuant n) : ℚ :=
  (∑ i : Fin n, x.val i ^ 2) * (∑ i : Fin n, y.val i ^ 2)
    - (∑ i : Fin n, x.val i * y.val i) ^ 2

-- 非负性：Lagrange 恒等式（Cauchy-Schwarz）
theorem areaSq_nonneg {n : ℕ} (x y : StateQuant n) : 0 ≤ areaSq x y := by
  unfold areaSq
  have hcs : (∑ i : Fin n, x.val i * y.val i) ^ 2 ≤ (∑ i : Fin n, x.val i ^ 2) * (∑ i : Fin n, y.val i ^ 2) := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin n => x.val i) (fun i : Fin n => y.val i))
  nlinarith

-- ============ 智能体的"盲区/洞（Hole）"与拓扑防御 ============
-- 真正的自我由"边界"和"盲区（洞）"定义。"洞"是那些无法与 ref 相长的外部输入
-- （正交或相消）。智能体的核心机制是"守卫自己的洞不被外物胡乱填平"。

-- 洞（Hole）：从记忆库中过滤出所有无法与 ref 相长的态量（正交或相消）
def Holes {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) : MemoryLibrary m :=
  lib.filter (fun x => (D x ref δ) = Interference.orthogonal ∨ (D x ref δ) = Interference.destructive)

-- 洞的纯粹性：Holes 里的每个元素与 ref 的关系都绝不是相长
lemma mem_holes_not_constructive {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) (x : StateQuant m)
    (hx : x ∈ Holes lib ref δ) : (D x ref δ) ≠ Interference.constructive := by
  unfold Holes at hx
  rw [List.mem_filter] at hx
  have hpx : (D x ref δ) = Interference.orthogonal ∨ (D x ref δ) = Interference.destructive :=
    of_decide_eq_true hx.2
  rcases hpx with hortho | hdest
  · rw [hortho]
    intro h
    cases h
  · rw [hdest]
    intro h
    cases h

-- 拓扑防御（Topological Defense）：洞无法夺舍。
-- 若 a 是 ref 的洞（正交 rank 1 或相消 rank 2），则 a 的 rank 恒 > 0，
-- 在 lexLe 排序中排在 ref（rank 0）之后，无论 a 放在哪里，ref 都稳居头部。
theorem hole_cannot_replace {n : ℕ} (lib : MemoryLibrary n) (ref a : StateQuant n) (δ : ℚ)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_hole : (D a ref δ) = Interference.orthogonal ∨ (D a ref δ) = Interference.destructive) :
    awaken (a :: ref :: lib) ref δ = some ref := by
  unfold IsSelf at h_self
  have h_rank_ref : (D ref ref δ).toRank = 0 := by
    rw [h_self]
    rfl
  have ha_gt : (D a ref δ).toRank > 0 := by
    rcases h_hole with hortho | hdest
    · rw [hortho]
      decide
    · rw [hdest]
      decide
  have h_head : ∃ rest, sortAgainst ref (ref :: lib) δ = ref :: rest :=
    ⟨sortAgainst ref lib δ, sortAgainst_head_cons ref δ lib h_rank_ref h_dom⟩
  have h_head' : ∃ rest', sortAgainst ref (a :: ref :: lib) δ = ref :: rest' :=
    sortAgainst_head_preserved ref δ a (ref :: lib) h_rank_ref ha_gt h_head
  rcases h_head' with ⟨rest', hrest'⟩
  unfold awaken
  rw [hrest']

-- ============ 洞与洞的交互（零成本派生，不换根） ============

-- 一、DiffPair 派生（不换根，只做派生概念）
def DiffPair (n : ℕ) := StateQuant n × StateQuant n

-- 二、Hole 结构：一个洞携带它的 ref 和盲区
structure Hole (m n : ℕ) where
  δ : ℚ
  ref : StateQuant n
  blind : MemoryLibrary m
  h_blind : ∀ x ∈ blind, (D x ref δ) ≠ Interference.constructive

-- 从 Holes 构造一个 Hole
def mkHole {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) : Hole m n where
  δ := δ
  ref := ref
  blind := Holes lib ref δ
  h_blind := by
    intro x hx
    exact mem_holes_not_constructive lib ref δ x hx

-- 三、两个洞的交互：A 的盲区在 B 的 ref 视角下是什么
-- 交互读数：A 的每个盲区元素，在 B 的参考系下对位成什么
/-
  holeInteract A B 把 A 的盲区放进 B 的 ref 视角下判断。
  依赖 D {m n} 的跨维语义，而 D 依赖 commonDist 的 min m n 截断。
  同上，commonDist 改了这里会跟着变。
-/
def holeInteract {m n k : ℕ} (A : Hole m n) (B : Hole k n) : List Interference :=
  A.blind.map (fun x => D (m := m) (n := n) x B.ref B.δ)

/-
  SameKindHole A B 表示"A 的盲区在 B 的视角下依然看不见"。
  注意这是方向性命题：SameKindHole A B 和 SameKindHole B A 是不同命题。
  A 看不见 B 的盲区，不代表 B 看不见 A 的盲区。
  same_kind_self 证了自反性（A 和自己是同类洞），但不证对称性。
-/
def SameKindHole {m n k : ℕ} (A : Hole m n) (B : Hole k n) : Prop :=
  ∀ r ∈ holeInteract A B, r ≠ Interference.constructive

-- 互补洞：A 的盲区在 B 视角下有相长的（B 能看见 A 的盲区）
def ComplementaryHole {m n k : ℕ} (A : Hole m n) (B : Hole k n) : Prop :=
  ∃ r ∈ holeInteract A B, r = Interference.constructive

-- 两个分类互斥
theorem same_comp_exclusive {m n k : ℕ} (A : Hole m n) (B : Hole k n) :
    SameKindHole A B → ¬ ComplementaryHole A B := by
  intro h_same h_comp
  rcases h_comp with ⟨r, hr_mem, hr_eq⟩
  exact h_same r hr_mem hr_eq

-- ============ 补丁：一个洞和自己是同类洞 ============

theorem same_kind_self {m n : ℕ} (A : Hole m n) : SameKindHole A A := by
  intro r hr
  unfold holeInteract at hr
  rcases List.mem_map.mp hr with ⟨x, hx, hx_eq⟩
  rw [← hx_eq]
  exact A.h_blind x hx

-- ============ 后果层：B 填补 A 的盲区 ============

-- 被 B 填补的部分
def filledBy {m n k : ℕ} (A : Hole m n) (B : Hole k n) : MemoryLibrary m :=
  A.blind.filter (fun x => decide ((D (m := m) (n := n) x B.ref B.δ) = Interference.constructive))

-- A 的新盲区 = 原盲区中，B 依然看不见的部分
def newBlind {m n k : ℕ} (A : Hole m n) (B : Hole k n) : MemoryLibrary m :=
  A.blind.filter (fun x => decide ((D (m := m) (n := n) x B.ref B.δ) ≠ Interference.constructive))

-- 同类洞：filledBy 为空
theorem same_kind_no_fill {m n k : ℕ} (A : Hole m n) (B : Hole k n)
    (h : SameKindHole A B) : filledBy A B = [] := by
  unfold filledBy
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  have hmem : (D (m := m) (n := n) x B.ref B.δ) ∈ holeInteract A B := by
    unfold holeInteract
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  have hne : ¬ ((D (m := m) (n := n) x B.ref B.δ) = Interference.constructive) :=
    h _ hmem
  simp [hne]

-- 互补洞：filledBy 非空
lemma complementary_filled_nonempty {m n k : ℕ} (A : Hole m n) (B : Hole k n)
    (h : ComplementaryHole A B) : filledBy A B ≠ [] := by
  intro hnil
  rcases h with ⟨r, hr_mem, hr_eq⟩
  unfold holeInteract at hr_mem
  rcases List.mem_map.mp hr_mem with ⟨x, hx_blind, hx_eq⟩
  have : x ∈ filledBy A B := by
    unfold filledBy
    rw [List.mem_filter]
    refine ⟨hx_blind, ?_⟩
    rw [hx_eq, hr_eq]
    decide
  rw [hnil] at this
  exact List.not_mem_nil this

-- 核心：互补洞交互后，盲区严格收缩
theorem complementary_reduces_hole {m n k : ℕ} (A : Hole m n) (B : Hole k n)
    (h : ComplementaryHole A B) :
    (newBlind A B).length < A.blind.length := by
  let p : StateQuant m → Bool := fun x => decide ((D (m := m) (n := n) x B.ref B.δ) = Interference.constructive)
  have hdecomp := List.length_eq_length_filter_add (l := A.blind) p
  have hdecomp' : A.blind.length = (filledBy A B).length + (newBlind A B).length := by
    simpa [filledBy, newBlind, p] using hdecomp
  have hnonempty : filledBy A B ≠ [] := complementary_filled_nonempty A B h
  have hlen_pos : 0 < (filledBy A B).length := List.length_pos_of_ne_nil hnonempty
  omega

-- 同类洞交互后，盲区长度不变
theorem same_kind_preserves_hole {m n k : ℕ} (A : Hole m n) (B : Hole k n)
    (h : SameKindHole A B) :
    (newBlind A B).length = A.blind.length := by
  let p : StateQuant m → Bool := fun x => decide ((D (m := m) (n := n) x B.ref B.δ) = Interference.constructive)
  have hdecomp := List.length_eq_length_filter_add (l := A.blind) p
  have hdecomp' : A.blind.length = (filledBy A B).length + (newBlind A B).length := by
    simpa [filledBy, newBlind, p] using hdecomp
  have hfill : filledBy A B = [] := same_kind_no_fill A B h
  rw [hfill] at hdecomp'
  simpa using hdecomp'.symm

-- ============ 截断定理：低维视角看不见高维的非公共维度 ============

/-
  截断是低维视角的宿命。当 m 和 n 不同时，commonDist 只在 Fin (min m n) 上求和，
  非公共维度（第 min m n 到 max m n - 1 维）的差异，在 D 的判定中完全不可见。

  这就是"对称是完全不对称的"的数学根：
  · D 本身对称（D_symm 已证）——但那只是公共维度上的对称。
  · 非公共维度上，低维看高维是截断（看不见），高维看低维是补全（看得见）。
  · 所以由 D 派生的洞交互（SameKindHole / ComplementaryHole）完全不对称：
    A 看 B 和 B 看 A 是两个不同命题，不是因为数学细节，是因为截断本身不对称。

  "互补"是单向的馈赠：高维能填低维的洞，低维填不了高维的洞。
-/

-- 截断的技术内容：如果两个 m 维态量在公共维度上相同，则 commonDist 相同
theorem commonDist_ignores_extra {m n : ℕ}
    (x1 x2 : StateQuant m) (y : StateQuant n)
    (h : ∀ i : Fin (min m n), x1.val (Fin.embedLeft i) = x2.val (Fin.embedLeft i)) :
    commonDist x1 y = commonDist x2 y := by
  unfold commonDist
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]

-- D 也不变（需要相位相同）
theorem D_ignores_extra {m n : ℕ} (x1 x2 : StateQuant m) (y : StateQuant n) (δ : ℚ)
    (h_val : ∀ i : Fin (min m n), x1.val (Fin.embedLeft i) = x2.val (Fin.embedLeft i))
    (h_phase : x1.phase = x2.phase) :
    D x1 y δ = D x2 y δ := by
  unfold D
  rw [commonDist_ignores_extra x1 x2 y h_val, h_phase]

-- 双向截断：如果两个 m 维态量和两个 n 维态量在公共维度上都相同，
-- 则 D 完全不变（无论非公共维度怎么变）
theorem D_only_depends_on_common {m n : ℕ}
    (x1 x2 : StateQuant m) (y1 y2 : StateQuant n) (δ : ℚ)
    (hx : ∀ i : Fin (min m n), x1.val (Fin.embedLeft i) = x2.val (Fin.embedLeft i))
    (hy : ∀ i : Fin (min m n), y1.val (Fin.embedRight i) = y2.val (Fin.embedRight i))
    (hx_phase : x1.phase = x2.phase)
    (hy_phase : y1.phase = y2.phase) :
    D x1 y1 δ = D x2 y2 δ := by
  unfold D
  have h_comm : commonDist x1 y1 = commonDist x2 y2 := by
    unfold commonDist
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i, hy i]
  rw [h_comm, hx_phase, hy_phase]

-- ============ 跨维面积：补 0 到 max 的 Gram 行列式 ============

/-
  跨维面积平方：x（m 维）和 y（n 维）张成的平行四边形面积平方。
  补 0 到 max m n，缺失维度视为 0——但这里的 0 不是虚假基准：
  补 0 后 |x'|² = |x|²、|y'|² = |y|²，y 在非公共维度的分量通过 |y|² 进入面积，
  即使内积在那些维度上贡献为 0。这是真实的张成，不是虚假基准。
-/

-- 补 0：把 StateQuant m 嵌入到 Fin k 上，i ≥ m 时为 0（k 为目标维度，通常为 max m n）
def valOrZero {m k : ℕ} (x : StateQuant m) (i : Fin k) : ℚ :=
  if h : i.val < m then x.val ⟨i.val, h⟩ else 0

-- ============ 跨维向量：差异在每一维（方向）上的量 ============

/-
  向量 = 差异的逐维读数（不是两点间的线段，是"每一维上的量"）。
  "差异不限维度，任意方向都有量" = 补 0 到 max m n 后逐维做差。

  这是"挂谷猜想"的离散版：挂谷要"任意方向都有线段"（全维），
  这里要"任意方向都有量"（跨维）——同一个结构。
-/

-- 跨维向量：补 0 到 max m n，逐维做差。
def crossDimVector {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : List ℚ :=
  (List.finRange (max m n)).map (fun i => valOrZero x i - valOrZero y i)

-- 跨维存在性（挂谷离散版）：任意方向（max m n 个维度）都有量。
theorem crossDimVector_length {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    (crossDimVector x y).length = max m n := by
  unfold crossDimVector
  simp [List.length_map, List.length_finRange]

-- 补 0 不改变体量（范数平方）：把 x 补 0 到 k 维（k ≥ m），normSq 不变。
-- "跨维不改变体量"——挂谷要"任意方向有线段"（全维），这里"任意方向有量"（跨维），
-- 但体量守恒。

-- 辅助引理：有限维上的求和，被截断到 m 维（补 0），等于只在前 m 维求和。
lemma sum_fin_pad {m k : ℕ} (f : Fin m → ℚ) (h : m ≤ k) :
    (∑ i : Fin k, (if hi : i.val < m then f ⟨i.val, hi⟩ else 0)) = ∑ i : Fin m, f i := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  have hleft : (∑ i ∈ Finset.range k, (if hk : i < k then (if hi : i < m then f ⟨i, hi⟩ else (0 : ℚ)) else 0))
      = ∑ i ∈ Finset.range k, (if hi : i < m then f ⟨i, hi⟩ else (0 : ℚ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hleft]
  rw [← Finset.sum_range_add_sum_Ico (fun i => if hi : i < m then f ⟨i, hi⟩ else (0 : ℚ)) h]
  have hico : (∑ i ∈ Finset.Ico m k, (if hi : i < m then f ⟨i, hi⟩ else (0 : ℚ))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Finset.mem_Ico.mp hi]
  rw [hico, add_zero]

theorem valOrZero_normSq {m k : ℕ} (x : StateQuant m) (h : m ≤ k) :
    (∑ i : Fin k, (valOrZero x i)^2) = normSq x := by
  unfold normSq
  simpa [valOrZero] using sum_fin_pad (fun i : Fin m => (x.val i)^2) h

-- ============ 向量收口：余弦定理（离散版） ============

/-
  向量这一层的收口定理。
  跨维内积 = 补 0 后的点积；非公共维有一方为 0，自动贡献 0，
  所以 ⟨x, y⟩_cross 只统计"公共维"上的相关性。

  余弦定理（离散）：
    |x − y|² = |x|² + |y|² − 2⟨x, y⟩

  "差异的体量 = 各自体量之和 − 2·相关"。
  这就是"任意方向都有量"（挂谷离散版）落地后，量如何守恒：
  差异不是凭空多出来的量，而是两部分体量相减相关而来。
  差异有限 ⇒ 差异的体量也有限、且可被各自体量与相关完全决定。
-/

-- 跨维内积：补 0 后逐维相乘求和。非公共维一方为 0，贡献 0。
def crossDot {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : ℚ :=
  ∑ i : Fin (max m n), valOrZero x i * valOrZero y i

-- 跨维向量模长平方：差异在每个方向上的量的平方和。
def crossDimNormSq {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : ℚ :=
  ∑ i : Fin (max m n), (valOrZero x i - valOrZero y i) ^ 2

-- 余弦定理（离散）：差异体量 = 各自体量 − 2·相关。
theorem crossDimNormSq_eq {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    crossDimNormSq x y = normSq x + normSq y - 2 * crossDot x y := by
  unfold crossDimNormSq crossDot
  have hx : (∑ i : Fin (max m n), valOrZero x i ^ 2) = normSq x :=
    valOrZero_normSq x (Nat.le_max_left m n)
  have hy : (∑ i : Fin (max m n), valOrZero y i ^ 2) = normSq y :=
    valOrZero_normSq y (Nat.le_max_right m n)
  calc
    (∑ i : Fin (max m n), (valOrZero x i - valOrZero y i) ^ 2)
        = ∑ i : Fin (max m n), (valOrZero x i ^ 2 - 2 * (valOrZero x i * valOrZero y i) + valOrZero y i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = ∑ i : Fin (max m n), (valOrZero x i ^ 2 - 2 * (valOrZero x i * valOrZero y i))
        + ∑ i : Fin (max m n), valOrZero y i ^ 2 := by
            rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin (max m n), valOrZero x i ^ 2
        - ∑ i : Fin (max m n), (2 * (valOrZero x i * valOrZero y i)))
        + ∑ i : Fin (max m n), valOrZero y i ^ 2 := by
            rw [Finset.sum_sub_distrib]
    _ = normSq x - 2 * (∑ i : Fin (max m n), valOrZero x i * valOrZero y i) + normSq y := by
            rw [hx, hy, Finset.mul_sum]
    _ = normSq x + normSq y - 2 * (∑ i : Fin (max m n), valOrZero x i * valOrZero y i) := by
            ring

-- 差异体量非负（平方和，恒非负）——余弦定理下等价于 Cauchy-Schwarz 的边界。
theorem crossDimNormSq_nonneg {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    0 ≤ crossDimNormSq x y := by
  unfold crossDimNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (valOrZero x i - valOrZero y i))

-- ============ 线段式向量：穿过暹界（处处有量） ============

/-
  昨天的 crossDimVector 是"端点差"——只取 x、y 两个点做差，中间是空的。
  这对应挂谷的"方向"：两个端点有量，方向就是差向量。

  但挂谷要的是"线段"：任意方向都有一整条处处有量的线段。
  "两点之间的每一个地方都必须确实有量"——这就是"暹界"（初步形式化）。

  用有理参数 t 从 0 走到 1，每一点都是 x、y 的凸组合（补 0 对齐）：
    t = 0  → x，t = 1 → y，t = 1/2 → 半值（中点）。
  全程 ℚ：t 取有理数，"处处"靠 ℚ 的稠密性（任意两有理数间还有有理数），
  不借 ℝ 的连续性。

  核心定理 crossDimPath_normSq：路径上任一点的体量都被端点完全决定——
    |P(t)|² = (1-t)²|x|² + 2t(1-t)⟨x,y⟩ + t²|y|²
  这是"处处有量"的解析式：差异的线段上没有一处是黑的，每一点都可名状。
-/

-- 有理参数化差异路径：t 走 0→1，每点一个跨维向量（凸组合）。
def crossDimPath {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (t : ℚ) : Fin (max m n) → ℚ :=
  fun i => (1 - t) * valOrZero x i + t * valOrZero y i

-- 路径上任一点的体量（范数平方）。
def pathNormSq {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (t : ℚ) : ℚ :=
  ∑ i : Fin (max m n), (crossDimPath x y t i)^2

-- 半值：暹界的中心点（t = 1/2）。
def midVal {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (i : Fin (max m n)) : ℚ :=
  crossDimPath x y (1 / 2 : ℚ) i

-- 端点退化：t = 0 退化为 x（补 0）。
theorem crossDimPath_zero {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    crossDimPath x y 0 = fun i => valOrZero x i := by
  unfold crossDimPath
  funext i
  ring

-- 端点退化：t = 1 退化为 y（补 0）。
theorem crossDimPath_one {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    crossDimPath x y 1 = fun i => valOrZero y i := by
  unfold crossDimPath
  funext i
  ring

-- 半值 = 中点：t = 1/2 时路径点是 (x_i + y_i) / 2。
theorem midVal_eq {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (i : Fin (max m n)) :
    midVal x y i = (valOrZero x i + valOrZero y i) / 2 := by
  unfold midVal crossDimPath
  ring

-- 端点差 = 差向量：路径首尾之差正是 crossDimVector 的逐维分量。
theorem crossDimPath_endpoint_diff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (i : Fin (max m n)) :
    crossDimPath x y 0 i - crossDimPath x y 1 i = valOrZero x i - valOrZero y i := by
  unfold crossDimPath
  ring

-- 核心：路径上任一点的体量 = 端点的凸二次型（处处有量的解析式）。
theorem crossDimPath_normSq {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (t : ℚ) :
    pathNormSq x y t = (1 - t)^2 * normSq x + 2 * t * (1 - t) * crossDot x y + t^2 * normSq y := by
  unfold pathNormSq crossDimPath
  have hx : (∑ i : Fin (max m n), valOrZero x i ^ 2) = normSq x :=
    valOrZero_normSq x (Nat.le_max_left m n)
  have hy : (∑ i : Fin (max m n), valOrZero y i ^ 2) = normSq y :=
    valOrZero_normSq y (Nat.le_max_right m n)
  calc
    (∑ i : Fin (max m n), ((1 - t) * valOrZero x i + t * valOrZero y i)^2)
        = ∑ i : Fin (max m n), ((1 - t)^2 * valOrZero x i ^ 2
            + (2 * t * (1 - t)) * (valOrZero x i * valOrZero y i)
            + t^2 * valOrZero y i ^ 2) := by
            apply Finset.sum_congr rfl; intro i hi; ring
    _ = ∑ i : Fin (max m n), ((1 - t)^2 * valOrZero x i ^ 2)
        + ∑ i : Fin (max m n), ((2 * t * (1 - t)) * (valOrZero x i * valOrZero y i))
        + ∑ i : Fin (max m n), (t^2 * valOrZero y i ^ 2) := by
            simp only [Finset.sum_add_distrib]
    _ = (1 - t)^2 * (∑ i : Fin (max m n), valOrZero x i ^ 2)
        + (2 * t * (1 - t)) * (∑ i : Fin (max m n), valOrZero x i * valOrZero y i)
        + t^2 * (∑ i : Fin (max m n), valOrZero y i ^ 2) := by
            simp only [Finset.mul_sum]
    _ = (1 - t)^2 * normSq x + 2 * t * (1 - t) * crossDot x y + t^2 * normSq y := by
            rw [hx, hy]
            rfl

-- 处处有量：路径上每一点的体量非负（线段上无一处是"黑"的）。
theorem crossDimPath_normSq_nonneg {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (t : ℚ) :
    0 ≤ pathNormSq x y t := by
  unfold pathNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (crossDimPath x y t i))

-- 跨维面积平方
def areaSqCross {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : ℚ :=
  (∑ i : Fin (max m n), valOrZero x i ^ 2) * (∑ i : Fin (max m n), valOrZero y i ^ 2)
    - (∑ i : Fin (max m n), valOrZero x i * valOrZero y i) ^ 2

-- 非负性：同一套 Cauchy-Schwarz，只是作用在补 0 后的向量上
theorem areaSqCross_nonneg {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    0 ≤ areaSqCross x y := by
  unfold areaSqCross
  have hcs : (∑ i : Fin (max m n), valOrZero x i * valOrZero y i) ^ 2
      ≤ (∑ i : Fin (max m n), valOrZero x i ^ 2) * (∑ i : Fin (max m n), valOrZero y i ^ 2) := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (valOrZero x) (valOrZero y))
  nlinarith

-- ============ 辅助引理：同维时 valOrZero 就是原值 ============

/-
  当 m = n = k 时，valOrZero x i 的 if 条件恒成立（i.val < n），
  所以 valOrZero x i = x.val i（Fin.eta）。
  这是 areaSqCross 退化回 areaSq 的核心桥梁。
-/
lemma valOrZero_self_dim {n : ℕ} (x : StateQuant n) (i : Fin n) :
    valOrZero x i = x.val i := by
  unfold valOrZero
  have h : i.val < n := i.isLt
  simp [h, Fin.eta]

-- 同维时，跨维面积退化回同维面积（桥接定理）
theorem areaSqCross_eq_areaSq {n : ℕ} (x y : StateQuant n) :
    areaSqCross x y = areaSq x y := by
  unfold areaSqCross areaSq
  rw [Nat.max_self]
  -- 现在两边都是 Fin n 上的求和
  -- 第一项：∑ valOrZero x i ^ 2 = ∑ x.val i ^ 2
  have h1 : (∑ i : Fin n, valOrZero x i ^ 2) = (∑ i : Fin n, x.val i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [valOrZero_self_dim]
  have h2 : (∑ i : Fin n, valOrZero y i ^ 2) = (∑ i : Fin n, y.val i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [valOrZero_self_dim]
  have h3 : (∑ i : Fin n, valOrZero x i * valOrZero y i)
          = (∑ i : Fin n, x.val i * y.val i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [valOrZero_self_dim, valOrZero_self_dim]
  rw [h1, h2, h3]

-- 跨维面积对称
theorem areaSqCross_symm {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    areaSqCross x y = areaSqCross y x := by
  unfold areaSqCross
  rw [← Nat.max_comm m n]
  -- 现在两边都是 Fin (max m n)
  -- 内积项：∑ (valOrZero x i * valOrZero y i) = ∑ (valOrZero y i * valOrZero x i)
  have h_inner : (∑ i : Fin (max m n), valOrZero x i * valOrZero y i)
               = (∑ i : Fin (max m n), valOrZero y i * valOrZero x i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_inner]
  ring

-- ============ s_rel 归位：有效差异计数（ℕ，测度） ============

/-
  s_rel 是测度，不是面积。公共维度上，有多少维 x_i ≠ y_i。
  这是 01 计数的精确形式：每一维是"有效差异（1）"或"无差异（0）"，s 数 1 的个数。
-/
def s_rel {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : ℕ :=
  (Finset.univ.filter (fun i : Fin (min m n) =>
    x.val (Fin.embedLeft i) ≠ y.val (Fin.embedRight i))).card

-- s_rel 有界：≤ 公共维度数
theorem s_rel_le_r_rel {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    s_rel x y ≤ min m n := by
  unfold s_rel
  simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin (min m n))))
    (p := fun i : Fin (min m n) => x.val (Fin.embedLeft i) ≠ y.val (Fin.embedRight i)))

-- ============ r_rel 归位：公共维度数（ℕ） ============

/-
  r_rel 是"坑的深度"——两人能对位的空间有多大。
  min m n 是公共维度数，s_rel ≤ r_rel 天然成立，s/r 落在 [0,1]。
-/
def r_rel {m n : ℕ} (_x : StateQuant m) (_y : StateQuant n) : ℕ :=
  min m n

-- ============ n_rel 归位：极性偏置读数（Bool） ============

/-
  n_rel 是"极性是否偏了"的布尔读数。
  · D = constructive（极性同向）→ false，中庸，不需要调节。
  · D = destructive（极性反向）→ true，偏了，往反方向拉。
  · D = orthogonal（不可比）→ true，无法判定的偏置，按"需要警惕"处理。
-/
def n_rel {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : Bool :=
  (D x y δ != Interference.constructive)

-- 旧 n_rel（toRank）改名保留：rankOf
def rankOf {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : ℕ :=
  (D x y δ).toRank

-- ============ 最深定理：IsSelf ↔ n_rel 为零 ============

/-
  静态版本：自我确认（IsSelf）当且仅当极性偏置读数为 false（中庸）。
  这不是新定理，是同一件事的两种写法——但它是"极性偏置"这根轴的形式化锚点。
-/
theorem IsSelf_iff_n_rel_false {n : ℕ} (ref : StateQuant n) (δ : ℚ) :
    IsSelf ref δ ↔ n_rel ref ref δ = false := by
  unfold IsSelf n_rel
  simp

-- ============ IsRelationStable 重定义：中庸即稳定 ============

/-
  关系稳定 = 极性偏置为零（中庸）。
  s_rel 和 r_rel 作为独立读数存在，不塞进判据——这是前面几轮注水的教训：
  把不同量纲的东西塞进一个不等式，必然造出假定理。
-/
def IsRelationStable {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : Prop :=
  n_rel x y δ = false

-- 自反稳定：ref 和自己是中庸的（由 IsSelf 推出）
theorem self_stable {n : ℕ} (ref : StateQuant n) (δ : ℚ) (h : IsSelf ref δ) :
    IsRelationStable ref ref δ := by
  unfold IsRelationStable
  exact (IsSelf_iff_n_rel_false ref δ).mp h

-- ============ 带阈值的态量（TypedStateQuant）与退化/子图包含 ============

-- 带阈值 δ 的态量
structure TypedStateQuant (n : ℕ) where
  δ : ℚ
  toStateQuant : StateQuant n

-- 用 min x.δ y.δ 作为阈值的对位
def D_typed {n : ℕ} (x y : TypedStateQuant n) : Interference :=
  D x.toStateQuant y.toStateQuant (min x.δ y.δ)

-- ============ 退化定理（方向 B） ============

theorem D_typed_eq_D_when_same_delta {n : ℕ} (x y : TypedStateQuant n)
    (h_delta : x.δ = y.δ) :
    D_typed x y = D x.toStateQuant y.toStateQuant x.δ := by
  unfold D_typed
  rw [h_delta, min_self]

-- ============ 子图包含定理（方向 A） ============

theorem untyped_edge_implies_typed_edge {n : ℕ} (V : Set (TypedStateQuant n)) (δ_min : ℚ)
    (h_global : ∀ x ∈ V, δ_min ≤ x.δ)
    (x y : V)
    (h_edge : D x.val.toStateQuant y.val.toStateQuant δ_min = Interference.constructive) :
    D_typed x.val y.val = Interference.constructive := by
  unfold D_typed
  have h_dist : commonDist x.val.toStateQuant y.val.toStateQuant ≤ δ_min := by
    by_contra h
    push Not at h
    unfold D at h_edge
    simp [h] at h_edge
  have h_min : δ_min ≤ min x.val.δ y.val.δ :=
    le_min (h_global x.val x.property) (h_global y.val y.property)
  have h_dist_min : commonDist x.val.toStateQuant y.val.toStateQuant ≤ min x.val.δ y.val.δ :=
    le_trans h_dist h_min
  unfold D
  rw [ite_eq_right (not_lt_of_ge h_dist_min)]
  unfold D at h_edge
  rw [ite_eq_right (not_lt_of_ge h_dist)] at h_edge
  exact h_edge

-- ============ s_rel 的读性质（仪表盘自身，不塞进 IsRelationStable） ============

-- s_rel = 0 当且仅当公共维度上完全相同
theorem s_rel_eq_zero_iff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    s_rel x y = 0 ↔ ∀ i : Fin (min m n), x.val (Fin.embedLeft i) = y.val (Fin.embedRight i) := by
  unfold s_rel
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i
    by_contra hne
    exact h (Finset.mem_univ i) hne
  · intro h i _
    exact fun hne => hne (h i)

-- s_rel = r_rel 当且仅当公共维度上每维都不同
theorem s_rel_eq_r_rel_iff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    s_rel x y = r_rel x y ↔ ∀ i : Fin (min m n),
      x.val (Fin.embedLeft i) ≠ y.val (Fin.embedRight i) := by
  unfold s_rel r_rel
  simpa using (Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin (min m n))))
    (p := fun i : Fin (min m n) => x.val (Fin.embedLeft i) ≠ y.val (Fin.embedRight i)))

-- ============ s_rel 与 commonDist 的独立性（计数大不等于距离大） ============

/-
  反例：两个态量的"有效差异计数"和"距离"是独立读数。
  · s_rel 大（每维都差一点）但 commonDist 小；
  · s_rel 小（只有一维差）但 commonDist 大。
-/
theorem s_rel_commonDist_independent :
    ∃ (x₁ y₁ x₂ y₂ : StateQuant 2),
      s_rel x₁ y₁ > s_rel x₂ y₂ ∧ commonDist x₁ y₁ < commonDist x₂ y₂ := by
  refine ⟨⟨![0, 0], .positive⟩, ⟨![1, 1], .positive⟩,
          ⟨![0, 0], .positive⟩, ⟨![100, 0], .positive⟩, ?_, ?_⟩
  · native_decide
  · native_decide

-- ============ 针穿洞的静态核：针的“穿过”只依赖公共维度 ============

/-
  针 needle : StateQuant m，洞的参考点 holeRef : StateQuant n。
  针“穿过”洞的判定是 D needle holeRef δ。
  由于 D 只看公共维度（D_only_depends_on_common），
  针在非公共维度上的分量，完全不影响“穿过”判定。
  这就是“针只能穿过洞的影子”——非公共部分针看不见。
-/

-- 把 m 维态量限制到公共维度（min m n）
def restrictToCommon {m n : ℕ} (x : StateQuant m) : StateQuant (min m n) :=
  { val := fun i => x.val (Fin.embedLeft i)
    phase := x.phase }

-- ============ 辅助：Fin 重索引与投影复合的搬运 ============

/-
  要证 D_eq_restrictToCommon，核心是把 commonDist (restrictToCommon needle) holeRef 的
  索引空间 Fin (min (min m n) n) 重索引到 Fin (min m n)（因为 min (min m n) n = min m n），
  并把 embedLeft/embedRight 的复合归位为「cast 后直接投影」。
  rw 在这里会因 motive 非 type-correct 卡住（索引参数依赖被重写的项），
  所以拆成三个小引理：求和 cast 不变、embedLeft 复合、embedRight 复合。
-/

-- cast 双射下的求和不变（Fin 重索引）
lemma sum_fin_cast {k₁ k₂ : ℕ} (h : k₁ = k₂) (f : Fin k₂ → ℚ) :
    (∑ i : Fin k₁, f (Fin.cast h i)) = ∑ i : Fin k₂, f i := by
  subst h
  simp

-- embedLeft 复合 = cast 后直接 embedLeft（投影只取 val，证明项被 Fin.ext 吸收）
lemma embedLeft_comp {m n : ℕ} (i : Fin (min (min m n) n)) :
    Fin.embedLeft (m := m) (n := n) (Fin.cast (Nat.min_eq_left (Nat.min_le_right m n)) i)
      = Fin.embedLeft (m := m) (n := n) (Fin.embedLeft (m := min m n) (n := n) i) := by
  apply Fin.ext
  simp [Fin.embedLeft]

-- embedRight 复合 = cast 后直接 embedRight
lemma embedRight_comp {m n : ℕ} (i : Fin (min (min m n) n)) :
    Fin.embedRight (m := m) (n := n) (Fin.cast (Nat.min_eq_left (Nat.min_le_right m n)) i)
      = Fin.embedRight (m := min m n) (n := n) i := by
  apply Fin.ext
  simp [Fin.embedRight]

-- 定理：D needle holeRef = D (restrictToCommon needle) holeRef
-- 即针的“穿过”判定，等价于它在公共维度上的投影对洞的判定
theorem D_eq_restrictToCommon {m n : ℕ} (needle : StateQuant m) (holeRef : StateQuant n) (δ : ℚ) :
    D needle holeRef δ = D (restrictToCommon (n := n) needle) holeRef δ := by
  unfold D
  have hcomm : commonDist needle holeRef = commonDist (restrictToCommon (n := n) needle) holeRef := by
    unfold commonDist restrictToCommon commonDim
    let h : min (min m n) n = min m n := Nat.min_eq_left (Nat.min_le_right m n)
    rw [← sum_fin_cast h]
    apply Finset.sum_congr rfl
    intro i _
    rw [embedLeft_comp i, embedRight_comp i]
  rw [hcomm, (show needle.phase = (restrictToCommon (n := n) needle).phase by rfl)]

-- 推论：针穿过洞的判定，完全由针在公共维度上的分量决定
-- 非公共维度的分量对“穿过”没有任何贡献
theorem pierce_depends_only_on_common {m n : ℕ} (needle₁ needle₂ : StateQuant m) (holeRef : StateQuant n) (δ : ℚ)
    (h_common : ∀ i : Fin (min m n), needle₁.val (Fin.embedLeft i) = needle₂.val (Fin.embedLeft i))
    (h_phase : needle₁.phase = needle₂.phase) :
    D needle₁ holeRef δ = D needle₂ holeRef δ :=
  D_only_depends_on_common needle₁ needle₂ holeRef holeRef δ h_common (fun _ => rfl) h_phase rfl

-- ============ 洞的极性偏置：洞里元素的 n_rel 必为 true ============

/-
  洞里的一切，在极性上都是偏的。
  Holes 的定义是 D x ref δ ≠ constructive（正交或相消），
  n_rel 的定义是 D x ref δ != constructive。
  所以洞里的元素，n_rel 必然是 true——它永远进不了排序的头部。
  这是"洞不进排序"的精确形式。
-/
theorem mem_holes_n_rel_true {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) (x : StateQuant m)
    (hx : x ∈ Holes lib ref δ) : n_rel x ref δ = true := by
  unfold n_rel
  have hne : D x ref δ ≠ Interference.constructive := mem_holes_not_constructive lib ref δ x hx
  simpa using hne

-- 推论：洞里的元素，永远不会在排序里排到 ref 前面
-- （因为 ref 的 n_rel = false（IsSelf 时），洞的 n_rel = true，rank 更大）
theorem holes_never_ahead {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ)
    (h_self : IsSelf ref δ) (x : StateQuant m) (hx : x ∈ Holes lib ref δ) :
    n_rel ref ref δ = false ∧ n_rel x ref δ = true := by
  refine ⟨?_, mem_holes_n_rel_true lib ref δ x hx⟩
  exact (IsSelf_iff_n_rel_false ref δ).mp h_self

-- ============ n_rel 和 rankOf 的桥接：Bool 读数 ↔ ℕ 等级 ============

/-
  n_rel 是极性偏置的 Bool 读数，rankOf 是排序用的 ℕ 等级。
  两者是同一个 D 读数的两个投影：
  · n_rel = false ↔ rankOf = 0（相长，中庸）
  · n_rel = true  ↔ rankOf ≥ 1（正交或相消，偏置）
  没有这条桥，"holes_never_ahead" 只在极性层成立，不在排序层成立。
-/
theorem n_rel_false_iff_rankOf_zero {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    n_rel x y δ = false ↔ rankOf x y δ = 0 := by
  unfold n_rel rankOf Interference.toRank
  cases D x y δ <;> simp

theorem n_rel_true_iff_rankOf_pos {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    n_rel x y δ = true ↔ rankOf x y δ > 0 := by
  unfold n_rel rankOf Interference.toRank
  cases D x y δ <;> simp

-- ============ 真正的"洞沉底"：用 rankOf 说话 ============

/-
  洞里元素在排序层的精确位置：rankOf 严格大于 ref 的 rankOf（= 0）。
  这才是 lexLe 里"洞排不到 ref 前面"的精确形式。
-/
theorem holes_rankOf_gt_ref {m n : ℕ} (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ)
    (h_self : IsSelf ref δ) (x : StateQuant m) (hx : x ∈ Holes lib ref δ) :
    rankOf ref ref δ < rankOf x ref δ := by
  have h_ref : n_rel ref ref δ = false := (IsSelf_iff_n_rel_false ref δ).mp h_self
  have h_x : n_rel x ref δ = true := mem_holes_n_rel_true lib ref δ x hx
  have h_ref0 : rankOf ref ref δ = 0 := (n_rel_false_iff_rankOf_zero ref ref δ).mp h_ref
  have h_xpos : rankOf x ref δ > 0 := (n_rel_true_iff_rankOf_pos x ref δ).mp h_x
  omega

-- ============ 轨迹：动态核的最小载体 ============

/-
  trajectory 是针在时间里的走法：每个时间步一个 StateQuant。
  它不是新的数据结构，是 evolve 的读数——但把它显式命名，
  才能谈"轨迹的某一步落进了洞"。
-/
def trajectory (m : ℕ) : Type := ℕ → StateQuant m

-- 轨迹在 t 时刻落进洞：这一步正好是洞里的元素
def hitsHole {m n : ℕ} (traj : trajectory m) (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) (t : ℕ) : Prop :=
  traj t ∈ Holes lib ref δ

-- ============ 最小定理一：轨迹进洞的那一刻，极性偏置被读出 ============

/-
  轨迹某一步落进洞，那一步的极性读数必然是 true（偏置）。
  这是"洞主导行为"的最小形式：轨迹走进去的那一刻，系统读到的是"偏了"。
  不是"洞拉住了轨迹"，是"轨迹进洞时，极性读数必然为 true"。
-/
theorem hit_hole_implies_biased {m n : ℕ} (traj : trajectory m) (lib : MemoryLibrary m)
    (ref : StateQuant n) (δ : ℚ) (t : ℕ) (h : hitsHole traj lib ref δ t) :
    n_rel (traj t) ref δ = true := by
  unfold hitsHole at h
  exact mem_holes_n_rel_true lib ref δ (traj t) h

-- ============ 最小定理二：进洞的那一步，排不到 ref 前面 ============

/-
  如果 ref 是自洽的（IsSelf），且轨迹在 t 时刻落进洞，
  那么 t 时刻的轨迹元素，在排序层（rankOf）严格排在 ref 后面。
  这是"洞沉底"在轨迹上的投影——轨迹进洞那一刻，它不在头部。
-/
theorem hit_hole_not_ahead {m n : ℕ} (traj : trajectory m) (lib : MemoryLibrary m)
    (ref : StateQuant n) (δ : ℚ) (t : ℕ)
    (h_self : IsSelf ref δ) (h : hitsHole traj lib ref δ t) :
    rankOf ref ref δ < rankOf (traj t) ref δ := by
  unfold hitsHole at h
  exact holes_rankOf_gt_ref lib ref δ h_self (traj t) h

-- ============ 最小定理三：轨迹的"洞时刻"集合 ============

/-
  轨迹的洞时刻集合：哪些时间步落进了洞。
  它是轨迹的一个可读子集——这是"轨迹被洞塑形"的第一个读数：
  不是"洞决定了轨迹怎么走"，是"洞标记了轨迹的哪些步是偏的"。
  塑形（洞决定轨迹怎么走）还是猜想；标记（哪些步偏了）现在能算。
-/
-- 洞时刻可判定：hitsHole 的 decidability 由 List.mem 的 LawfulBEq 判定给出
instance hitsHoleDecidable {m n : ℕ} (traj : trajectory m) (lib : MemoryLibrary m) (ref : StateQuant n) (δ : ℚ) (t : ℕ) :
    Decidable (hitsHole traj lib ref δ t) :=
  List.instDecidableMemOfLawfulBEq (traj t) (Holes lib ref δ)

def holeMoments {m n : ℕ} (traj : trajectory m) (lib : MemoryLibrary m)
    (ref : StateQuant n) (δ : ℚ) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t => hitsHole traj lib ref δ t)

-- 洞时刻集合里的每一步，极性读数都是 true
theorem holeMoments_biased {m n : ℕ} (traj : trajectory m) (lib : MemoryLibrary m)
    (ref : StateQuant n) (δ : ℚ) (T t : ℕ) (h : t ∈ holeMoments traj lib ref δ T) :
    n_rel (traj t) ref δ = true := by
  unfold holeMoments at h
  rw [Finset.mem_filter] at h
  exact hit_hole_implies_biased traj lib ref δ t h.2

-- ============ 一、轨迹接上 evolve：egoTrajectory ============

/-
  egoTrajectory 是"自我轨迹"：每一步 = 那一刻 awaken 出来的东西。
  它不是任意序列，是"辨别→排序→选择"三步跑出来的生成规则。
  空库兜底返回 ref（awaken 返回 none 时）。
-/
def egoTrajectory {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n)
    (inputs : ℕ → StateQuant n) (δ : ℚ) : trajectory n :=
  fun t =>
    match awaken (evolve (ref :: lib) inputs δ t) ref δ with
    | some x => x
    | none => ref

-- ============ 二、洞被排除：ref 稳定时，轨迹不落进洞 ============

/-
  洞被排除（"主导"的最弱可证版）：
  如果 ref 自洽（IsSelf）、支配初始库、所有输入 rank > 0，
  那么 egoTrajectory 的每一步都是 ref，而 ref 不在洞里。
  所以轨迹的每一步都不落进洞——洞不是被"穿过"，是被"排除"。
-/
theorem egoTrajectory_eq_ref {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs : ∀ t, (D (inputs t) ref δ).toRank > 0)
    (t : ℕ) :
    egoTrajectory lib ref inputs δ t = ref := by
  unfold egoTrajectory
  -- 用 I_am_always_I：awaken (evolve ...) = some ref
  have h := I_am_always_I lib ref δ inputs h_self h_dom h_inputs t
  rw [h]

/-
  洞被排除的推论：轨迹的每一步都不在洞里。
  因为轨迹每一步都是 ref，而 ref 不在洞里
  （ref 对 ref 是 constructive，Holes 要求 ≠ constructive）。
-/
theorem egoTrajectory_not_in_holes {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs : ∀ t, (D (inputs t) ref δ).toRank > 0)
    (t : ℕ) :
    egoTrajectory lib ref inputs δ t ∉ Holes lib ref δ := by
  rw [egoTrajectory_eq_ref lib ref δ inputs h_self h_dom h_inputs t]
  -- ref ∉ Holes lib ref δ：因为 ref 对 ref 是 constructive
  intro h
  have hne : D ref ref δ ≠ Interference.constructive := mem_holes_not_constructive lib ref δ ref h
  unfold IsSelf at h_self
  exact hne h_self

-- ============ 三、洞时刻集合为空 ============

/-
  ref 稳定时，轨迹的洞时刻集合为空——轨迹从不进洞。
  holeMoments 的定义已存在：哪些时间步落进洞。
-/
theorem egoTrajectory_holeMoments_empty {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs : ∀ t, (D (inputs t) ref δ).toRank > 0)
    (T : ℕ) :
    holeMoments (egoTrajectory lib ref inputs δ) lib ref δ T = ∅ := by
  unfold holeMoments
  apply Finset.filter_eq_empty_iff.mpr
  intro t _
  -- t 不在洞时刻：egoTrajectory t ∉ Holes
  unfold hitsHole
  exact egoTrajectory_not_in_holes lib ref δ inputs h_self h_dom h_inputs t

-- ============ 放宽版：允许同阶输入，只要体量被压制，洞时刻仍空 ============

/-
  放宽版洞时刻为空：
  前提从"所有输入 rank > 0"（I_am_always_I）放宽到
  "同阶输入体量严格小于 ref"（temporal_solid_immunity）。
  结论不变：轨迹每一步仍是 ref，洞时刻集合仍为空。
  这是"洞被排除"的更强版本——不是没有同阶挑战，是挑战体量不够，被压制。
-/
theorem egoTrajectory_holeMoments_empty_relaxed {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n)
    (h_self : IsSelf ref δ)
    (h_dom : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_mass : ∀ t, (D (inputs t) ref δ).toRank = 0 → normSq ref > normSq (inputs t))
    (T : ℕ) :
    holeMoments (egoTrajectory lib ref inputs δ) lib ref δ T = ∅ := by
  unfold holeMoments
  apply Finset.filter_eq_empty_iff.mpr
  intro t _
  unfold hitsHole
  -- 轨迹 t = ref（用 temporal_solid_immunity）
  have h_traj : egoTrajectory lib ref inputs δ t = ref := by
    unfold egoTrajectory
    have h := temporal_solid_immunity lib ref δ inputs h_self h_dom h_inputs_mass t
    rw [h]
  rw [h_traj]
  -- ref ∉ Holes lib ref δ
  intro h
  have hne : D ref ref δ ≠ Interference.constructive := mem_holes_not_constructive lib ref δ ref h
  unfold IsSelf at h_self
  exact hne h_self

-- ============ 夺舍后，旧 ref 沉入新参考点的洞 ============

/-
  意志夺舍，表象更替：
  时刻 t 发生 temporal_ego_replacement（inputs t 体量 ≥ ref 且同阶），
  从 t+1 起，awaken 返回的是 inputs t（新表象），不再是 ref（旧表象）。
  而旧表象 ref，在新表象的参考系下，如果相位不同向，就落进了它的洞。
  这就是"意志完成夺舍，旧表象沉入新表象的盲区"。
-/
theorem ref_falls_into_replacer_hole {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n) (t : ℕ)
    (_h_self : IsSelf ref δ)
    (_h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (_h_inputs_before : ∀ k < t, (D (inputs k) ref δ).toRank > 0)
    (_h_input_t_rank0 : (D (inputs t) ref δ).toRank = 0)
    (_h_input_t_mass : normSq (inputs t) ≥ normSq ref)
    (h_phase_diff : D ref (inputs t) δ ≠ Interference.constructive) :
    ref ∈ Holes (ref :: lib) (inputs t) δ := by
  unfold Holes
  rw [List.mem_filter]
  refine ⟨List.mem_cons_self, ?_⟩
  -- 需要证：decide (D ref (inputs t) δ = orthogonal ∨ destructive) = true
  -- 由 h_phase_diff：D ref (inputs t) δ ≠ constructive，三态穷举
  cases h : D ref (inputs t) δ with
  | constructive => exfalso; exact h_phase_diff h
  | orthogonal => simp
  | destructive => simp

-- ============ 轨迹的不可逆：夺舍前后轨迹不同 ============

/-
  赌场机制：局部判定可逆（D 是函数），但全局轨迹不可逆。
  夺舍前，轨迹 t = ref；夺舍后，轨迹 (t+1) = inputs t。
  如果 inputs t ≠ ref，则轨迹在夺舍前后不同——全局不可逆。
-/
theorem trajectory_irreversible_after_replacement {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n) (t : ℕ)
    (h_self : IsSelf ref δ)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_before : ∀ k < t, (D (inputs k) ref δ).toRank > 0)
    (h_input_t_rank0 : (D (inputs t) ref δ).toRank = 0)
    (h_input_t_mass : normSq (inputs t) ≥ normSq ref)
    (h_ne : inputs t ≠ ref) :
    egoTrajectory lib ref inputs δ (t + 1) = inputs t ∧
    egoTrajectory lib ref inputs δ (t + 1) ≠ ref := by
  have h_awaken := temporal_ego_replacement lib ref δ inputs t h_self h_dom_lib
    h_inputs_before h_input_t_rank0 h_input_t_mass
  -- temporal_ego_replacement 给出 awaken (evolve ... (t+1)) = some (inputs t)
  -- 所以 egoTrajectory (t+1) = inputs t
  have h_traj : egoTrajectory lib ref inputs δ (t + 1) = inputs t := by
    unfold egoTrajectory
    rw [h_awaken]
  refine ⟨h_traj, ?_⟩
  rw [h_traj]
  exact h_ne

-- ============ 辅助引理：同维时 s_rel 化简 ============

/-
  同维时 min n n = n，embedLeft/embedRight 都是恒等嵌入，
  s_rel 化简为"有多少维 x_i ≠ y_i"。
-/
-- 辅助：Fin.cast 下的 filter 计数不变（重索引）
lemma filter_fin_cast_card {k₁ k₂ : ℕ} (h : k₁ = k₂) (p : Fin k₂ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin k₁ => p (Fin.cast h i))).card
    = (Finset.univ.filter p).card := by
  subst h
  simp

-- 辅助：同维时 embedLeft/embedRight 就是 Fin.cast（恒等嵌入）
lemma embedLeft_same_dim {n : ℕ} (i : Fin (min n n)) :
    Fin.embedLeft (m := n) (n := n) i = Fin.cast (Nat.min_self n) i := by
  apply Fin.ext
  simp [Fin.embedLeft]

lemma embedRight_same_dim {n : ℕ} (i : Fin (min n n)) :
    Fin.embedRight (m := n) (n := n) i = Fin.cast (Nat.min_self n) i := by
  apply Fin.ext
  simp [Fin.embedRight]

lemma s_rel_same_dim {n : ℕ} (x y : StateQuant n) :
    s_rel x y = (Finset.univ.filter (fun i : Fin n => x.val i ≠ y.val i)).card := by
  unfold s_rel
  let h : min n n = n := Nat.min_self n
  rw [← filter_fin_cast_card h (fun i : Fin n => x.val i ≠ y.val i)]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  rw [embedLeft_same_dim i, embedRight_same_dim i]

-- 同维时 commonDist 也化简（平方和逐维）
lemma commonDist_same_dim {n : ℕ} (x y : StateQuant n) :
    commonDist x y = ∑ i : Fin n, (x.val i - y.val i)^2 := by
  unfold commonDist commonDim
  let h : min n n = n := Nat.min_self n
  rw [← sum_fin_cast h (fun i : Fin n => (x.val i - y.val i)^2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [embedLeft_same_dim i, embedRight_same_dim i]

-- ============ 结论一：s_rel 的三角不等式（同维） ============

/-
  测度的定义性性质：d(x,z) ≤ d(x,y) + d(y,z)。
  对每个 i，x_i ≠ z_i 蕴含 x_i ≠ y_i 或 y_i ≠ z_i。
  所以"x 和 z 不同的维" ⊆ "x 和 y 不同的维" ∪ "y 和 z 不同的维"。
  计数上：左边 ≤ 右边两个计数之和。
-/
theorem s_rel_triangle {n : ℕ} (x y z : StateQuant n) :
    s_rel x z ≤ s_rel x y + s_rel y z := by
  rw [s_rel_same_dim, s_rel_same_dim, s_rel_same_dim]
  have h_sub : (Finset.univ.filter (fun i : Fin n => x.val i ≠ z.val i))
      ⊆ ((Finset.univ.filter (fun i : Fin n => x.val i ≠ y.val i))
        ∪ (Finset.univ.filter (fun i : Fin n => y.val i ≠ z.val i))) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hxz : x.val i ≠ z.val i := hi.2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hxy : x.val i ≠ y.val i
    · left
      exact ⟨Finset.mem_univ i, hxy⟩
    · right
      have hxy_eq : x.val i = y.val i := by
        by_contra hne
        exact hxy hne
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hyz_eq
      exact hxz (by rw [hxy_eq, hyz_eq])
  have h_card := Finset.card_le_card h_sub
  have h_union := Finset.card_union_le (Finset.univ.filter (fun i : Fin n => x.val i ≠ y.val i))
    (Finset.univ.filter (fun i : Fin n => y.val i ≠ z.val i))
  exact le_trans h_card h_union

-- ============ 结论二：零测度的两个读数一致（同维） ============

/-
  s_rel = 0 ⟺ 每维相同 ⟺ commonDist = 0（平方和为 0）。
  计数读数和距离读数在零处一致——这是"差异作为测度"的零基准。
-/
theorem s_rel_zero_iff_commonDist_zero {n : ℕ} (x y : StateQuant n) :
    s_rel x y = 0 ↔ commonDist x y = 0 := by
  rw [s_rel_same_dim, commonDist_same_dim]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    have hxy : x.val i = y.val i := by
      by_contra hne
      exact h (Finset.mem_univ i) hne
    rw [hxy]
    simp
  · intro hd i _ hne
    have h0 : (x.val i - y.val i)^2 = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => (x.val i - y.val i)^2) (fun i _ => sq_nonneg _)).mp hd
      exact hall i (Finset.mem_univ i)
    have hdiff : x.val i - y.val i = 0 := sq_eq_zero_iff.mp h0
    exact hne (sub_eq_zero.mp hdiff)

-- ============ 一、夺舍后的新赌局：新参考点自己的洞时刻 ============

/-
  夺舍后的轨迹：从 t+1 起，egoTrajectory 恒为 inputs t（新表象）。
  问题：新表象自己稳不稳？它对"自己"是否落进自己的洞？
-/

/-
  可证的核心：下一时刻（s = t+1），新参考点不进自己的洞。
  由 temporal_ego_replacement，egoTrajectory (t+1) = inputs t；
  inputs t 自洽（IsSelf），对"自己"是 constructive，而洞要求 ≠ constructive，矛盾。
-/
lemma replacer_not_in_own_hole_at_next {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n) (t : ℕ)
    (h_self : IsSelf ref δ)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_before : ∀ k < t, (D (inputs k) ref δ).toRank > 0)
    (h_input_t_rank0 : (D (inputs t) ref δ).toRank = 0)
    (h_input_t_mass : normSq (inputs t) ≥ normSq ref)
    (h_replacer_self : IsSelf (inputs t) δ) :
    egoTrajectory lib ref inputs δ (t + 1) ∉ Holes (inputs t :: lib) (inputs t) δ := by
  have h_awaken := temporal_ego_replacement lib ref δ inputs t h_self h_dom_lib
    h_inputs_before h_input_t_rank0 h_input_t_mass
  have h_traj : egoTrajectory lib ref inputs δ (t + 1) = inputs t := by
    unfold egoTrajectory
    rw [h_awaken]
  rw [h_traj]
  intro h
  have hne : D (inputs t) (inputs t) δ ≠ Interference.constructive :=
    mem_holes_not_constructive (inputs t :: lib) (inputs t) δ (inputs t) h
  unfold IsSelf at h_replacer_self
  exact hne h_replacer_self

/-
  补全前提，清掉最后一条 sorry。

  注意一个关键纠正：egoTrajectory 的排序参考点始终是 ref（lexLe ref δ），
  所以"后续输入不冲击 inputs t"的前提取的应该是 **ref 视角**的 rank
  （(D (inputs k) ref δ).toRank > 0），而不是 inputs t 视角。
  用户给出的 h_inputs_after 写成了 inputs t 视角，这里纠正为 ref 视角——
  因为要证的是 inputs t 在 ref 排序下稳居头部。
-/

-- 推广的 head 保持：head（rank 0 于 ref 视角）在头部，插入 a（rank > 0 于 ref 视角），head 保持
lemma sortAgainst_head_preserved_gen {n : ℕ} (ref head a : StateQuant n) (δ : ℚ) (l : MemoryLibrary n)
    (h_head_rank0 : (D head ref δ).toRank = 0)
    (ha_gt : (D a ref δ).toRank > 0)
    (h_head : ∃ rest, sortAgainst ref l δ = head :: rest) :
    ∃ rest', sortAgainst ref (a :: l) δ = head :: rest' :=
  sortAgainst_head_preserved_notle ref head a δ l
    (by
      unfold lexLe
      rintro (hlt | ⟨heq, _⟩)
      · exact (not_lt_of_gt (by simpa [h_head_rank0] using ha_gt)) hlt
      · exact (ne_of_gt (by simpa [h_head_rank0] using ha_gt)) heq)
    h_head

-- 从 t+1 起，inputs t（rank 0 于 ref 视角）在 ref 排序下稳居头部
lemma replacer_head_from_t_plus_1 {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n) (t : ℕ)
    (h_self : IsSelf ref δ)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_before : ∀ k < t, (D (inputs k) ref δ).toRank > 0)
    (h_input_t_rank0 : (D (inputs t) ref δ).toRank = 0)
    (h_input_t_mass : normSq (inputs t) ≥ normSq ref)
    (h_inputs_after : ∀ k > t, (D (inputs k) ref δ).toRank > 0) :
    ∀ s, t + 1 ≤ s → ∃ rest, sortAgainst ref (evolve (ref :: lib) inputs δ s) δ = inputs t :: rest := by
  intro s hs
  refine Nat.le_induction (m := t + 1)
    (P := fun n _ => ∃ rest, sortAgainst ref (evolve (ref :: lib) inputs δ n) δ = inputs t :: rest)
    ?_ ?_ s hs
  · -- base：s = t+1，由 temporal_ego_replacement 给出 awaken = some (inputs t)
    have h_awaken := temporal_ego_replacement lib ref δ inputs t h_self h_dom_lib
      h_inputs_before h_input_t_rank0 h_input_t_mass
    unfold awaken at h_awaken
    cases hsort : sortAgainst ref (evolve (ref :: lib) inputs δ (t + 1)) δ with
    | nil => simp [hsort] at h_awaken
    | cons b rest =>
        simp [hsort] at h_awaken
        exact ⟨rest, by rw [h_awaken]⟩
  · -- succ：n ≥ t+1，插入 inputs n（rank > 0 于 ref 视角），inputs t 保持头部
    intro n hn ih
    have ha_gt : (D (inputs n) ref δ).toRank > 0 := h_inputs_after n (by omega)
    have hstep := sortAgainst_head_preserved_gen ref (inputs t) (inputs n) δ
      (evolve (ref :: lib) inputs δ n) h_input_t_rank0 ha_gt ih
    simpa [evolve, step] using hstep

/-
  补全前提后：只要后续输入在 ref 视角下 rank 恒 > 0（不冲击 inputs t），
  从 t+1 起轨迹恒为 inputs t，而 inputs t 自洽（不进自己的洞），
  所以轨迹在 inputs t 的洞里没有时刻。
-/
theorem replacer_stable_after_replacement {n : ℕ} (lib : MemoryLibrary n) (ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n) (t : ℕ)
    (h_self : IsSelf ref δ)
    (h_dom_lib : ∀ x ∈ lib, (D x ref δ).toRank = 0 → normSq ref ≥ normSq x)
    (h_inputs_before : ∀ k < t, (D (inputs k) ref δ).toRank > 0)
    (h_input_t_rank0 : (D (inputs t) ref δ).toRank = 0)
    (h_input_t_mass : normSq (inputs t) ≥ normSq ref)
    (h_replacer_self : IsSelf (inputs t) δ)
    (h_inputs_after : ∀ k > t, (D (inputs k) ref δ).toRank > 0)
    (s : ℕ) (hs : t + 1 ≤ s) :
    egoTrajectory lib ref inputs δ s ∉ Holes (inputs t :: lib) (inputs t) δ := by
  have h_head := replacer_head_from_t_plus_1 lib ref δ inputs t h_self h_dom_lib
    h_inputs_before h_input_t_rank0 h_input_t_mass h_inputs_after s hs
  have h_traj : egoTrajectory lib ref inputs δ s = inputs t := by
    unfold egoTrajectory awaken
    rcases h_head with ⟨rest, hrest⟩
    rw [hrest]
  rw [h_traj]
  intro h
  have hne : D (inputs t) (inputs t) δ ≠ Interference.constructive :=
    mem_holes_not_constructive (inputs t :: lib) (inputs t) δ (inputs t) h
  unfold IsSelf at h_replacer_self
  exact hne h_replacer_self

/-
  新表象自己不自洽时，它自己也落进自己的洞——新赌局一开始就是输的。
-/
theorem replacer_not_self_falls_in_own_hole {n : ℕ} (lib : MemoryLibrary n) (_ref : StateQuant n) (δ : ℚ)
    (inputs : ℕ → StateQuant n) (t : ℕ)
    (h_not_self : ¬ IsSelf (inputs t) δ) :
    inputs t ∈ Holes (inputs t :: lib) (inputs t) δ := by
  unfold Holes
  rw [List.mem_filter]
  refine ⟨List.mem_cons_self, ?_⟩
  -- ¬ IsSelf (inputs t) δ = D (inputs t) (inputs t) δ ≠ constructive
  unfold IsSelf at h_not_self
  cases h : D (inputs t) (inputs t) δ with
  | constructive => exfalso; exact h_not_self h
  | orthogonal => simp
  | destructive => simp

-- ============ 二、跨维反例：s_rel 三角不等式在跨维时失效 ============

/-
  跨维反例：s_rel x z > s_rel x y + s_rel y z。
  x, z 是 5 维且每维都不同（s_rel = 5）；
  y 是 1 维，和 x、z 的公共维度只有 1 维（s_rel ≤ 1）。
  所以 5 > 1 + 1 = 2。
  这钉死"s_rel 只在同维内是测度"。
-/
theorem s_rel_triangle_fails_cross_dim :
    ∃ (x z : StateQuant 5) (y : StateQuant 1),
      s_rel x z > s_rel x y + s_rel y z := by
  refine ⟨⟨fun _ => 0, .positive⟩, ⟨fun _ => 1, .positive⟩, ⟨fun _ => 0, .positive⟩, ?_⟩
  native_decide

-- ============ 红利二：零差异 + 相位不对 ⟹ 进洞 ============

/-
  这是"洞 = 零差异 + 相位不对"的精确形式。
  如果 x 和 ref 在每一维都相同（s_rel = 0），但相位不是同号
  （不同号，或有一方是中性），那么 x 落进 ref 的洞。
  · 零差异本身不进洞——如果相位同号，是相长。
  · 相位不对才进洞——正交或相消。
-/
theorem zero_diff_phase_mismatch_in_hole {n : ℕ} (lib : MemoryLibrary n) (ref x : StateQuant n) (δ : ℚ)
    (hδ : 0 ≤ δ)
    (h_zero : s_rel x ref = 0)
    (h_phase : ¬ (x.phase = Phase.positive ∧ ref.phase = Phase.positive) ∧
               ¬ (x.phase = Phase.negative ∧ ref.phase = Phase.negative)) :
    x ∈ Holes (x :: lib) ref δ := by
  unfold Holes
  rw [List.mem_filter]
  refine ⟨List.mem_cons_self, ?_⟩
  -- 1. s_rel = 0 → commonDist = 0
  have h_dist : commonDist x ref = 0 := (s_rel_zero_iff_commonDist_zero x ref).mp h_zero
  -- 2. 0 ≤ δ → ¬ (commonDist > δ)
  have h_not_gt : ¬ (commonDist x ref > δ) := by rw [h_dist]; linarith
  -- 3. D 走 else 分支，只判相位
  unfold D
  rw [ite_eq_right h_not_gt]
  -- 4. 相位穷举，h_phase 排除两个同号分支
  cases hx : x.phase <;> cases hr : ref.phase <;> simp [hx, hr] at h_phase ⊢

-- ============ 引理：D 判正交 ⟹ 进洞 ============

/-
  正交的元素，必然在洞里——这是 Holes 定义的直接推论。
  Holes 的成员条件是 D = orthogonal ∨ D = destructive，
  正交满足第一个析取项。
-/
lemma orthogonal_mem_holes {n : ℕ} (lib : MemoryLibrary n) (ref x : StateQuant n) (δ : ℚ)
    (h : D x ref δ = Interference.orthogonal) :
    x ∈ Holes (x :: lib) ref δ := by
  unfold Holes
  rw [List.mem_filter]
  refine ⟨List.mem_cons_self, ?_⟩
  simp [h]

-- ============ 洞的第二种来源：差异大，不管相位，直接进洞 ============

/-
  差异大（commonDist > δ）时，D 走 then 分支返回 orthogonal，
  与相位无关——所以不管相位同号还是不同号，都进洞。
  这是洞的第二种来源：不是"太相同但立场相反"（第一种），是"太不同，看不见"。
-/
theorem large_diff_in_hole {n : ℕ} (lib : MemoryLibrary n) (ref x : StateQuant n) (δ : ℚ)
    (h_diff : commonDist x ref > δ) :
    x ∈ Holes (x :: lib) ref δ := by
  apply orthogonal_mem_holes
  unfold D
  rw [ite_eq_left h_diff]

-- ============ 可选：洞的两种来源的总结（文档性定理） ============

/-
  洞的两种来源：
  · 差异大（commonDist > δ）：不管相位，D 判正交，进洞（large_diff_in_hole）。
  · 差异为零但相位不对：D 走 else 分支判相消/正交，进洞（zero_diff_phase_mismatch_in_hole）。
  两者覆盖了洞的主要来源——"太不同"和"太相同但立场相反"。
-/
theorem hole_two_sources {n : ℕ} (lib : MemoryLibrary n) (ref x : StateQuant n) (δ : ℚ)
    (hδ : 0 ≤ δ) :
    (commonDist x ref > δ → x ∈ Holes (x :: lib) ref δ) ∧
    (s_rel x ref = 0 →
      ¬ (x.phase = Phase.positive ∧ ref.phase = Phase.positive) →
      ¬ (x.phase = Phase.negative ∧ ref.phase = Phase.negative) →
      x ∈ Holes (x :: lib) ref δ) := by
  refine ⟨?_, ?_⟩
  · exact large_diff_in_hole lib ref x δ
  · intro h_zero h_phase1 h_phase2
    exact zero_diff_phase_mismatch_in_hole lib ref x δ hδ h_zero ⟨h_phase1, h_phase2⟩

-- ============ 辅助引理：D 判相消或正交 ⟹ 进洞 ============

/-
  这是 orthogonal_mem_holes 的对称版：只要 D 是正交或相消（不进相长），就进洞。
-/
lemma orthogonal_or_destructive_mem_holes {n : ℕ} (lib : MemoryLibrary n) (ref x : StateQuant n) (δ : ℚ)
    (h : D x ref δ = Interference.orthogonal ∨ D x ref δ = Interference.destructive) :
    x ∈ Holes (x :: lib) ref δ := by
  unfold Holes
  rw [List.mem_filter]
  exact ⟨List.mem_cons_self, by simpa using h⟩

-- ============ 第二种来源的完整版：距离在 δ 内 + 相位不对 ⟹ 进洞 ============

/-
  第二种来源的完整形式：
  commonDist ≤ δ（距离在容差内），但相位不同向（正/负、正/中性、负/中性……）。
  这时 D 走 else 分支，判相消或正交，进洞。
  zero_diff_phase_mismatch_in_hole 是它的特例（commonDist = 0，即 s_rel = 0）。
-/
theorem phase_mismatch_in_hole {n : ℕ} (lib : MemoryLibrary n) (ref x : StateQuant n) (δ : ℚ)
    (h_dist : commonDist x ref ≤ δ)
    (h_phase : ¬ (x.phase = Phase.positive ∧ ref.phase = Phase.positive) ∧
               ¬ (x.phase = Phase.negative ∧ ref.phase = Phase.negative)) :
    x ∈ Holes (x :: lib) ref δ := by
  apply orthogonal_or_destructive_mem_holes
  unfold D
  rw [ite_eq_right (not_lt_of_ge h_dist)]
  -- 相位穷举，h_phase 排除两个相长分支
  cases hx : x.phase <;> cases hr : ref.phase <;> simp [hx, hr] at h_phase ⊢

-- ============ 层的一般理论（几何无关的骨架） ============

/-
  【层的一般理论：任何"对称的不可区分关系"都长出同一个层】

  差异论的"层"不依赖几何（色环的环距离、状态空间的欧氏距离都一样）。
  它只依赖一件事：**一个对称的不可区分关系 r**。因为 r 通常不传递
  （距离不满足三角不等式），所以必须取传递闭包；对称性保证闭包成等价关系；
  等价关系给出商（凝结对象）；层定律（粘合满射 + 零损失 ⟺ 无新合并）随之成立。

  下面先把这套骨架一次性建好，色环 / 状态空间 / 未来的任何几何都只是代入。
-/

-- 任何"对称的不可区分关系"的传递闭包都是等价关系。
theorem reflTransGen_equivalence {α : Type*} {r : α → α → Prop}
    (hsym : ∀ a b, r a b → r b a) :
    Equivalence (Relation.ReflTransGen r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; exact Relation.ReflTransGen.refl
  · intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (hsym _ _ hbc)) ih
  · intro a b c hab hbc
    exact Relation.ReflTransGen.trans hab hbc

-- 传递闭包同构（通用）：逐点等价的关系，其传递闭包也逐点等价。
-- 用于色环（ℕ 阈值）与层几何（ℚ 阈值）之间的桥。
theorem reflTransGen_congr {α : Type*} {r s : α → α → Prop} (h : ∀ a b, r a b ↔ s a b) :
    ∀ a b, Relation.ReflTransGen r a b ↔ Relation.ReflTransGen s a b := by
  intro a b
  constructor
  · intro hx
    induction hx with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih => exact Relation.ReflTransGen.tail ih ((h _ _).mp hbc)
  · intro hx
    induction hx with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih => exact Relation.ReflTransGen.tail ih ((h _ _).mpr hbc)

-- 传递闭包单调（通用）：细关系 ⊆ 粗关系 ⟹ 传递闭包同样包含。
-- 这是 sameHueClassTrans_mono / ResLayer.related_mono 的统一形式。
theorem reflTransGen_mono {α : Type*} {r₁ r₂ : α → α → Prop}
    (hsub : ∀ a b, r₁ a b → r₂ a b) :
    ∀ a b, Relation.ReflTransGen r₁ a b → Relation.ReflTransGen r₂ a b := by
  intro a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact Relation.ReflTransGen.tail ih (hsub _ _ hbc)

-- 凝结商（统一版）：不可区分关系的传递闭包所成的商。
def closureSetoid {α : Type*} (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a) : Setoid α :=
  Setoid.mk (Relation.ReflTransGen r) (reflTransGen_equivalence hsym)

-- 凝结映射（统一版）：细关系 → 粗关系的商映射。
def closureMap {α : Type*} {r₁ r₂ : α → α → Prop} (hsub : ∀ a b, r₁ a b → r₂ a b)
    (hs₁ : ∀ a b, r₁ a b → r₁ b a) (hs₂ : ∀ a b, r₂ a b → r₂ b a) :
    Quotient (closureSetoid r₁ hs₁) → Quotient (closureSetoid r₂ hs₂) :=
  Quotient.map id (reflTransGen_mono hsub)

-- 统一的粘合律（sheaf 公理的一般形式）：对称关系的传递闭包下，
-- 一串相邻相容的元素必首尾同类。与几何无关（任何 r 都成立）。
theorem gluing_general {α : Type*} {r : α → α → Prop} {f : ℕ → α} {k : ℕ}
    (h : ∀ i, i < k → r (f i) (f (i + 1))) :
    Relation.ReflTransGen r (f 0) (f k) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
      have h₁ : Relation.ReflTransGen r (f 0) (f k) :=
        ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      exact Relation.ReflTransGen.tail h₁ (h k (Nat.lt_succ_self k))

-- 层的统一定律：细关系 r₁ ⊆ 粗关系 r₂ 时，凝结映射 (a) 满射、(b) 单射 ⟺ 无新合并。
-- 这一条同时覆盖色环（hueDist）和状态空间（commonDist）——**层与几何无关**。
theorem layer_law {α : Type*} {r₁ r₂ : α → α → Prop}
    (hsub : ∀ a b, r₁ a b → r₂ a b)
    (hs₁ : ∀ a b, r₁ a b → r₁ b a) (hs₂ : ∀ a b, r₂ a b → r₂ b a) :
    Function.Surjective (closureMap hsub hs₁ hs₂) ∧
    (Function.Injective (closureMap hsub hs₁ hs₂) ↔
      ∀ a b, Relation.ReflTransGen r₂ a b → Relation.ReflTransGen r₁ a b) := by
  constructor
  · -- (a) 满射：任一粗层类都来自某个细层类
    intro q
    induction q using Quotient.ind with
    | _ x => exact ⟨Quotient.mk (closureSetoid r₁ hs₁) x, rfl⟩
  · constructor
    · -- (b→) 单射 ⟹ 无新合并
      intro hinj a b hab
      have hq : (Quotient.mk (closureSetoid r₁ hs₁) a : Quotient (closureSetoid r₁ hs₁)) =
          Quotient.mk (closureSetoid r₁ hs₁) b := by
        apply hinj
        show (Quotient.mk (closureSetoid r₂ hs₂) a : Quotient (closureSetoid r₂ hs₂)) =
          Quotient.mk (closureSetoid r₂ hs₂) b
        exact Quotient.sound hab
      exact Quotient.exact hq
    · -- (b←) 无新合并 ⟹ 单射
      intro hback q₁ q₂ hq
      induction q₁ using Quotient.ind with
      | _ x =>
        induction q₂ using Quotient.ind with
        | _ y =>
          have hxy : Relation.ReflTransGen r₂ x y := Quotient.exact hq
          exact Quotient.sound (hback x y hxy)

-- ============ 层几何（LayerGeometry）：层的抽象骨架 ============

/-
  【层几何：把"层"从具体几何里剥出来】

  差异论有两个几何：色环（hueDist）、状态空间（commonDist）。
  它们表面不同，但"层"的部分完全一样。把它抽成一个结构：

    LayerGeometry α :=
      一族按粗糙度 δ 参数化的对称不可区分关系 indist，
      且随 δ 单调（δ 大 = 粗 = 看得更少 = 不可区分更多）。

  有了这个结构，"层"的全部定理（等价关系 / 单调 / 凝结 / 粘合 / 层定律）
  都是对任意 LayerGeometry 的普遍事实——具体几何只是代入。
-/

-- 层几何：按 δ 参数化的对称、单调的不可区分关系族。
structure LayerGeometry (α : Type*) where
  indist : ℚ → α → α → Prop
  h_symm : ∀ δ a b, indist δ a b → indist δ b a
  h_mono : ∀ δ₁ δ₂ : ℚ, δ₁ ≤ δ₂ → ∀ a b, indist δ₁ a b → indist δ₂ a b

namespace LayerGeometry

variable {α : Type*}

-- 层 δ 下的"同类"：不可区分的传递闭包。
def related (G : LayerGeometry α) (δ : ℚ) (a b : α) : Prop :=
  Relation.ReflTransGen (G.indist δ) a b

-- 同类是等价关系（对任何层几何都成立）。
theorem related_equiv (G : LayerGeometry α) (δ : ℚ) : Equivalence (G.related δ) :=
  reflTransGen_equivalence (G.h_symm δ)

-- 凝结商：层 δ 的同类等价类。
def setoid (G : LayerGeometry α) (δ : ℚ) : Setoid α :=
  closureSetoid (G.indist δ) (G.h_symm δ)

-- 同类单调：δ 增大（变粗），同类扩张。
theorem related_mono (G : LayerGeometry α) {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) {a b : α}
    (hab : G.related δ₁ a b) : G.related δ₂ a b :=
  reflTransGen_mono (G.h_mono δ₁ δ₂ h) a b hab

-- 凝结映射：细层 δ₁ → 粗层 δ₂ 的商映射。
def condense (G : LayerGeometry α) {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    Quotient (G.setoid δ₁) → Quotient (G.setoid δ₂) :=
  closureMap (G.h_mono δ₁ δ₂ h) (G.h_symm δ₁) (G.h_symm δ₂)

-- 层定律（满射）：任何层几何的凝结都满射。
theorem condense_surjective (G : LayerGeometry α) {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    Function.Surjective (G.condense h) :=
  (layer_law (G.h_mono δ₁ δ₂ h) (G.h_symm δ₁) (G.h_symm δ₂)).1

-- 层定律（零损失刻画）：凝结单射 ⟺ 没有新合并。
theorem condense_injective_iff (G : LayerGeometry α) {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    Function.Injective (G.condense h) ↔
      ∀ a b, G.related δ₂ a b → G.related δ₁ a b :=
  (layer_law (G.h_mono δ₁ δ₂ h) (G.h_symm δ₁) (G.h_symm δ₂)).2

-- 粘合律：局部相容 ⟹ 首尾同类（sheaf 公理，任意层几何）。
theorem gluing (G : LayerGeometry α) (δ : ℚ) {f : ℕ → α} {k : ℕ}
    (h : ∀ i, i < k → G.indist δ (f i) (f (i + 1))) :
    G.related δ (f 0) (f k) :=
  gluing_general h

end LayerGeometry

-- ============ 一、离散色环：循环距离 ============

/-
  色环是圈，不是线。Fin k 上定义循环距离：
  两点在环上的最短路径长度（绕过去可能更短）。
-/
def hueDist {k : ℕ} (a b : Fin k) : ℕ :=
  let d := (a.val + k - b.val) % k
  min d (k - d)

-- 自反：自己和自己距离 0
theorem hueDist_self {k : ℕ} (a : Fin k) : hueDist a a = 0 := by
  unfold hueDist
  simp [Nat.mod_self]

-- 辅助：hueDist 等于线距离与绕环距离的较小者
lemma hueDist_eq_min_dist {k : ℕ} (a b : Fin k) :
    hueDist a b = min (Nat.dist a.val b.val) (k - Nat.dist a.val b.val) := by
  unfold hueDist
  by_cases h : a.val ≤ b.val
  · have hdist : Nat.dist a.val b.val = b.val - a.val := Nat.dist_eq_sub_of_le h
    rw [hdist]
    by_cases h0 : a.val = b.val
    · rw [h0]
      simp
    · have hlt_mod : k - (b.val - a.val) < k := by omega
      have hab : a.val + k - b.val = k - (b.val - a.val) := by omega
      have hkk : k - (k - (b.val - a.val)) = b.val - a.val := by omega
      rw [hab, Nat.mod_eq_of_lt hlt_mod]
      simp [hkk, min_comm]
  · have hgt : b.val < a.val := lt_of_not_ge h
    have hdist : Nat.dist a.val b.val = a.val - b.val := by
      rw [Nat.dist_comm]
      exact Nat.dist_eq_sub_of_le (le_of_lt hgt)
    rw [hdist]
    have hlt_mod : a.val - b.val < k := by omega
    have hab : a.val + k - b.val = k + (a.val - b.val) := by omega
    rw [hab, Nat.add_comm k (a.val - b.val), Nat.add_mod_right, Nat.mod_eq_of_lt hlt_mod]

-- 对称：a 到 b 的距离 = b 到 a 的距离
theorem hueDist_symm {k : ℕ} (a b : Fin k) : hueDist a b = hueDist b a := by
  rw [hueDist_eq_min_dist, hueDist_eq_min_dist]
  rw [Nat.dist_comm]

-- 有界：环上距离不超过 k/2
theorem hueDist_le_half {k : ℕ} (a b : Fin k) : hueDist a b ≤ k / 2 := by
  unfold hueDist
  let d := (a.val + k - b.val) % k
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
  have hd : d < k := Nat.mod_lt _ hk
  rw [min_le_iff]
  omega

-- ============ 三、截断即类型：定义 + 第一个真发现 ============

/-
  截断即类型：在分辨率 δ 下，两个色块"同类型"。
  这是"颜色截断成色名"的直接形式化。
-/
def sameHueClass {k : ℕ} (a b : Fin k) (δ : ℕ) : Prop :=
  hueDist a b ≤ δ

-- （自反 / 对称两条包装已删：sameHueClass 就是 hueDist ≤ δ，
--   直接用 hueDist_self / hueDist_symm；传递性由通用层论统一处理。）

-- ============ 真发现：截断不自动传递 ============

/-
  关键发现：sameHueClass 不是等价关系——传递性失败。
  这不是 bug，是"截断即类型"必须面对的困难：
  分辨率 δ 下，A 和 B 同色，B 和 C 同色，但 A 和 C 可能不同色。
  就像颜色渐变：深红和红同色，红和橙红同色，但深红和橙红不同色。
-/
theorem sameHueClass_not_trans :
    ¬ ∀ (a b c : Fin 12) (δ : ℕ),
      sameHueClass a b δ → sameHueClass b c δ → sameHueClass a c δ := by
  intro h
  have h01 : sameHueClass (⟨0, by omega⟩ : Fin 12) (⟨2, by omega⟩ : Fin 12) 2 := by
    norm_num [sameHueClass, hueDist]
  have h12 : sameHueClass (⟨2, by omega⟩ : Fin 12) (⟨4, by omega⟩ : Fin 12) 2 := by
    norm_num [sameHueClass, hueDist]
  have h02 : sameHueClass (⟨0, by omega⟩ : Fin 12) (⟨4, by omega⟩ : Fin 12) 2 := by
    exact h (⟨0, by omega⟩ : Fin 12) (⟨2, by omega⟩ : Fin 12) (⟨4, by omega⟩ : Fin 12) 2 h01 h12
  have h02_false : ¬ sameHueClass (⟨0, by omega⟩ : Fin 12) (⟨4, by omega⟩ : Fin 12) 2 := by
    norm_num [sameHueClass, hueDist]
  exact h02_false h02

-- ============ 一、分辨率单调性：δ 大，类宽 ============

/-
  静态分布 + 自反调整的第一层：
  δ 越大，sameHueClass 越宽容——原本同色的，放宽后仍同色。
  这就是"自反调整放宽分辨率"的单调性。
-/
theorem sameHueClass_mono {k : ℕ} (a b : Fin k) (δ₁ δ₂ : ℕ) (h : δ₁ ≤ δ₂)
    (hc : sameHueClass a b δ₁) : sameHueClass a b δ₂ := by
  unfold sameHueClass at hc ⊢
  exact le_trans hc h

-- ============ 二、漂移的边界：自反不能无限收窄 ============

/-
  自反收窄有一个下界：δ = 0 时，只有自己和自己同类。
  这钉死了"漂移不能消灭所有类"——最低分辨率下，类型退化成"每个点自己一类"。
  这是"静态分布"的极限：δ = 0 时，类边界退化成点。
-/
theorem sameHueClass_at_zero {k : ℕ} (a b : Fin k) :
    sameHueClass a b 0 ↔ a = b := by
  unfold sameHueClass hueDist
  constructor
  · intro h
    have h0 : min ((a.val + k - b.val) % k) (k - (a.val + k - b.val) % k) = 0 :=
      Nat.le_zero.mp h
    have hk : 0 < k := a.pos
    have hmod : (a.val + k - b.val) % k < k := Nat.mod_lt _ hk
    rcases Nat.min_eq_zero_iff.mp h0 with hd | hkd
    · -- d = 0 ⟹ a.val = b.val
      have hdiv : k ∣ a.val + k - b.val := Nat.dvd_of_mod_eq_zero hd
      have hpos : 0 < a.val + k - b.val := by omega
      have hge : k ≤ a.val + k - b.val := Nat.le_of_dvd hpos hdiv
      have hlt : a.val + k - b.val < 2 * k := by omega
      rcases hdiv with ⟨m, hm⟩
      have hm_pos : 0 < m := by
        rw [hm] at hpos
        exact Nat.pos_of_mul_pos_left hpos
      have hm_le : m ≤ 1 := by
        have hlt' : k * m < k * 2 := by
          rw [hm] at hlt
          simpa [Nat.mul_comm] using hlt
        exact Nat.le_of_lt_succ ((Nat.mul_lt_mul_left hk).mp hlt')
      have hm_eq : m = 1 := by omega
      have hn : a.val + k - b.val = k := by
        simpa [hm_eq] using hm
      exact Fin.ext (by omega)
    · -- k - d = 0 ⟹ d = k，与 d < k 矛盾
      have hge : k ≤ (a.val + k - b.val) % k := Nat.sub_eq_zero_iff_le.mp hkd
      omega
  · intro h
    rw [h]
    simp

-- ============ 半值猜想：hueDist 就是两个色块的"半值" ============

/-
  《半值猜想》原文："0 到 1 之间存在 n 个半值，每个半值不是 0.5 的数值，
  而是差异环上恰好处于阈值的差异节点簇。"

  色环版：hueDist a b 就是 a 和 b 之间的"半值"——
  它是 sameHueClass a b 首次成立的最小分辨率。
  半值不是数值 0.5，是临界步数 hueDist a b。
-/

-- 半值恰好是临界点：在 hueDist 处成立，低于它不成立
theorem halfValue_critical {k : ℕ} (a b : Fin k) :
    sameHueClass a b (hueDist a b) ∧
    (∀ δ : ℕ, δ < hueDist a b → ¬ sameHueClass a b δ) := by
  constructor
  · unfold sameHueClass
    exact le_rfl
  · intro δ hδ
    unfold sameHueClass
    exact not_le.mpr hδ

-- 半值为零 ⟺ 同一个色块
theorem halfValue_zero_iff {k : ℕ} (a b : Fin k) :
    hueDist a b = 0 ↔ a = b := by
  have h := sameHueClass_at_zero a b
  unfold sameHueClass at h
  rwa [Nat.le_zero] at h

-- ============ 传递闭包：δ 图上连得上的就是同类 ============

/-
  sameHueClass 不传递（sameHueClass_not_trans），不能直接建 Quotient。
  但传递闭包 ReflTransGen 自动传递——它定义的是"通过一串 δ 内的步能走到"。
  这就是"连通分量"：在图（节点=色块，边=δ 内同色）上连得上的，就是同类。
  这绕开了不传递死结，同时保留了"局部粘连"的结构。
-/
def sameHueClassTrans {k : ℕ} (a b : Fin k) (δ : ℕ) : Prop :=
  Relation.ReflTransGen (fun x y => sameHueClass x y δ) a b

-- （自反 / 传递 / 单步三条包装已删：直接用 Relation.ReflTransGen.refl / .trans / .single，
--   sameHueClassTrans 就是它的缩写，无需再包装一层。）

-- ============ 最小差异原理：连通分量单调 ============

/-
  最小差异原理的色环版：
  δ 增大时，原有的边不会消失（sameHueClass_mono），
  所以原有的连通分量不会断——δ₁ 下连通的，δ₂（更大）下仍连通。
  这就是"层次聚类单调性"：δ 增大只会合并类，不会拆分类。
-/
theorem sameHueClassTrans_mono {k : ℕ} (a b : Fin k) (δ₁ δ₂ : ℕ) (h : δ₁ ≤ δ₂)
    (hc : sameHueClassTrans a b δ₁) : sameHueClassTrans a b δ₂ :=
  reflTransGen_mono (fun _ _ hx => sameHueClass_mono _ _ δ₁ δ₂ h hx) a b hc

-- ============ 连通分量是等价关系（自动传递） ============

/-
  和 sameHueClass 不同，sameHueClassTrans 是等价关系：
  自反、对称、传递都成立。
  所以"类型 = 连通分量"这条路是通的——Quotient 能建了。
  这正是绕开 sameHueClass_not_trans 的方式：
  类型不是"δ 直接截断的等价类"，是"δ 图上连通的等价类"。
-/
-- 等价关系（实例）：色环的同类是"对称关系（色距 ≤ δ）的传递闭包"，
-- 直接由通用引理 reflTransGen_equivalence 给出（旧的手写归纳已删）。
theorem sameHueClassTrans_equivalence {k : ℕ} (δ : ℕ) :
    Equivalence (sameHueClassTrans (k := k) · · δ) :=
  reflTransGen_equivalence (fun a b h => by
    show hueDist b a ≤ δ
    rw [← hueDist_symm a b]
    exact h)

-- ============ 一、类数 ≤ 总量（组合事实，有内容） ============

/-
  Quotient 的类数不超过元素数。
  这是"每个类非空 + 类两两不交"的直接结果，不是 trivial 的。
  需要 Quotient 的 Fintype 实例（依赖 DecidableRel）。
-/

-- ============ 可达性（通用）：有限图上 ReflTransGen 的可判定性 ============

/-
  【通用 BFS：任何有限关系上的传递闭包都可判定】

  这一块原先是给 sameHueClassTrans 手写的 135 行 BFS。
  但"传递闭包可判定"与色环无关——任何有限类型上的可判定关系都成立。
  抽成通用版本后：色环只是它的一行实例；
  以后任何层（ResLayer.related 等）想要可判定性也白拿。
-/

-- 一步扩张：把 S 中元素一步能到的点并进来。
def stepSet {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (S : Finset α) : Finset α :=
  S ∪ S.biUnion (fun x => Finset.univ.filter (fun y => r x y))

-- 至多 n 步可达集合。
def reachIter {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r] :
    ℕ → Finset α → Finset α
  | 0, S => S
  | n + 1, S => stepSet r (reachIter r n S)

-- stepSet 的成员刻画：在 S 里，或从 S 的某点一步可达。
lemma mem_stepSet {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (S : Finset α) (y : α) :
    y ∈ stepSet r S ↔ y ∈ S ∨ ∃ x ∈ S, r x y := by
  unfold stepSet
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]

-- 递推展开（定义等式）。
lemma reachIter_succ {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (n : ℕ) (S : Finset α) :
    reachIter r (n+1) S = stepSet r (reachIter r n S) := rfl

-- 单调：n 步 ⊆ n+1 步。
lemma reachIter_subset_succ {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (n : ℕ) (S : Finset α) :
    reachIter r n S ⊆ reachIter r (n+1) S := by
  intro b hb
  exact Finset.mem_union.mpr (Or.inl hb)

-- 单调（广义）：n ≤ m ⟹ n 步 ⊆ m 步。
lemma reachIter_mono_le {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (S : Finset α) {n m : ℕ} (h : n ≤ m) :
    reachIter r n S ⊆ reachIter r m S := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih => exact Finset.Subset.trans ih (reachIter_subset_succ r m S)

-- 基数上界：可达集合 ≤ Fintype.card α。
lemma reachIter_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (n : ℕ) (S : Finset α) :
    (reachIter r n S).card ≤ Fintype.card α :=
  le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)

-- 通用引理：单调递增、上界为 k 的自然数序列，必存在相邻相等（不动点）。
lemma exists_adjacent_eq {k : ℕ} (f : ℕ → ℕ)
    (hmono : ∀ n, f n ≤ f (n+1))
    (hbound : f (k+1) ≤ k) :
    ∃ n ≤ k, f n = f (n+1) := by
  by_contra h
  have hne : ∀ n ≤ k, f n ≠ f (n+1) := by
    intro n hn he
    exact h ⟨n, hn, he⟩
  have hstrict : ∀ n ≤ k, f n < f (n+1) := by
    intro n hn
    exact lt_of_le_of_ne (hmono n) (hne n hn)
  have hge : ∀ n ≤ k + 1, n ≤ f n := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hlt : f n < f (n+1) := hstrict n (by omega)
        omega
  exact (not_le_of_gt (Nat.lt_of_succ_le (hge (k+1) (le_rfl)))) hbound

-- 不动点传播：一旦相邻相等，之后不再增长。
lemma reachIter_fixed_propagates {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (S : Finset α) {n : ℕ}
    (h : reachIter r n S = reachIter r (n+1) S) :
    ∀ m, n ≤ m → reachIter r m S = reachIter r n S := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [reachIter_succ, ih]
      rw [reachIter_succ] at h
      exact h.symm

-- 收敛：card α + 1 步 ⊆ card α 步（基数有界 ⟹ 必然饱和）。
lemma reachIter_converges {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (S : Finset α) :
    reachIter r (Fintype.card α + 1) S ⊆ reachIter r (Fintype.card α) S := by
  let f : ℕ → ℕ := fun n => (reachIter r n S).card
  have hmono : ∀ n, f n ≤ f (n+1) :=
    fun n => Finset.card_le_card (reachIter_subset_succ r n S)
  have hbound : f (Fintype.card α + 1) ≤ Fintype.card α :=
    reachIter_card_le r (Fintype.card α + 1) S
  obtain ⟨n, hn, heq⟩ := exists_adjacent_eq f hmono hbound
  have hfixed : reachIter r n S = reachIter r (n+1) S := by
    apply Finset.eq_of_subset_of_card_le (reachIter_subset_succ r n S)
    exact le_of_eq heq.symm
  have hprop : reachIter r (Fintype.card α + 1) S = reachIter r n S :=
    reachIter_fixed_propagates r S hfixed (Fintype.card α + 1) (by omega)
  have hsub : reachIter r n S ⊆ reachIter r (Fintype.card α) S :=
    reachIter_mono_le r S (by omega)
  rw [hprop]
  exact hsub

-- 闭包：card α 步集合在 r 一步下封闭。
lemma reachIter_closed {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (S : Finset α) {b : α}
    (h : ∃ c ∈ reachIter r (Fintype.card α) S, r c b) :
    b ∈ reachIter r (Fintype.card α) S := by
  rcases h with ⟨c, hc, hcb⟩
  have hb' : b ∈ reachIter r (Fintype.card α + 1) S := by
    rw [reachIter_succ, mem_stepSet]
    exact Or.inr ⟨c, hc, hcb⟩
  exact reachIter_converges r S hb'

-- 可靠性：n 步可达 ⟹ 从 S 某点出发的传递闭包。
lemma reachIter_sound {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] :
    ∀ (n : ℕ) (S : Finset α) (b : α), b ∈ reachIter r n S →
      ∃ a ∈ S, Relation.ReflTransGen r a b := by
  intro n
  induction n with
  | zero =>
      intro S b hb
      exact ⟨b, hb, Relation.ReflTransGen.refl⟩
  | succ n ih =>
      intro S b hb
      rw [reachIter_succ, mem_stepSet] at hb
      rcases hb with hb | ⟨c, hc, hcb⟩
      · exact ih S b hb
      · obtain ⟨a, ha, hac⟩ := ih S c hc
        exact ⟨a, ha, Relation.ReflTransGen.tail hac hcb⟩

-- 双向等价：传递闭包 ⟺ card α 步可达。
theorem reflTransGen_iff_reachIter {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (a b : α) :
    Relation.ReflTransGen r a b ↔ b ∈ reachIter r (Fintype.card α) {a} := by
  constructor
  · intro h
    refine Relation.ReflTransGen.rec
      (motive := fun c _ => c ∈ reachIter r (Fintype.card α) {a}) ?_ ?_ h
    · exact reachIter_mono_le r _ (Nat.zero_le _) (Finset.mem_singleton_self a)
    · intro x y _ hyz ih
      exact reachIter_closed r _ ⟨x, ih, hyz⟩
  · intro h
    obtain ⟨a', ha', h⟩ := reachIter_sound r (Fintype.card α) {a} b h
    rw [Finset.mem_singleton] at ha'
    rw [← ha']
    exact h

-- 通用实例：有限类型上任何可判定关系的传递闭包都可判定。
instance reflTransGen_decidable {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] : DecidableRel (Relation.ReflTransGen r) := by
  intro a b
  exact decidable_of_iff (b ∈ reachIter r (Fintype.card α) {a})
    (reflTransGen_iff_reachIter r a b).symm

-- 色环单步关系的可判定性（色距比较）。
instance sameHueClass_decidable {k : ℕ} (δ : ℕ) :
    DecidableRel (sameHueClass (k := k) · · δ) := by
  intro a b
  unfold sameHueClass
  infer_instance

-- 色环的同类的可判定性 = 通用实例（原来的 135 行 BFS 已删）。
instance sameHueClassTrans_decidable {k δ : ℕ} :
    DecidableRel (sameHueClassTrans (k := k) · · δ) :=
  fun a b => reflTransGen_decidable (r := fun x y : Fin k => sameHueClass x y δ) a b

-- 类数定义
def classCount {k : ℕ} (δ : ℕ) : ℕ :=
  let s : Setoid (Fin k) := Setoid.mk (sameHueClassTrans (k := k) · · δ) (sameHueClassTrans_equivalence δ)
  letI : DecidableRel s.r := sameHueClassTrans_decidable
  Fintype.card (Quotient s)

-- 类数 ≤ k（核心组合事实）
theorem classCount_le_k {k : ℕ} (δ : ℕ) : classCount (k := k) δ ≤ k := by
  unfold classCount
  have hle := @Fintype.card_quotient_le (Fin k) (Fin.fintype k)
    (Setoid.mk (sameHueClassTrans (k := k) · · δ) (sameHueClassTrans_equivalence δ))
    sameHueClassTrans_decidable
  simpa [Fintype.card_fin] using hle

-- classCount 反单调（澄明随 δ 变浊）：δ 增大，连通分量合并，类数减少。
-- 层次聚类单调性：δ 增大只合并类、不拆分类——澄明（类数）单调递减。
set_option linter.style.haveILetI false in
theorem classCount_antitone {k : ℕ} {δ₁ δ₂ : ℕ} (h : δ₁ ≤ δ₂) :
    classCount (k := k) δ₂ ≤ classCount (k := k) δ₁ := by
  unfold classCount
  letI : DecidableRel (sameHueClassTrans (k := k) · · δ₁) := sameHueClassTrans_decidable
  letI : DecidableRel (sameHueClassTrans (k := k) · · δ₂) := sameHueClassTrans_decidable
  let f : Quotient (Setoid.mk (sameHueClassTrans (k := k) · · δ₁) (sameHueClassTrans_equivalence δ₁)) →
           Quotient (Setoid.mk (sameHueClassTrans (k := k) · · δ₂) (sameHueClassTrans_equivalence δ₂)) :=
    Quotient.map id (fun a b hab => sameHueClassTrans_mono a b δ₁ δ₂ h hab)
  have hsurj : Function.Surjective f := by
    exact Quotient.map_surjective (fun a b hab => sameHueClassTrans_mono a b δ₁ δ₂ h hab) (fun y => ⟨y, rfl⟩)
  exact Fintype.card_le_of_surjective f hsurj

-- 消解损失为零 ⟺ 不合并任何类（有限 H⁰ 的精确刻画，色环版）。
-- 类数不变 ⟺ 粗层的每个"同类"在细层就已同类——即消解没有造成任何信息损失。
set_option linter.style.haveILetI false in
theorem classCount_loss_zero_iff {k : ℕ} {δ₁ δ₂ : ℕ} (h : δ₁ ≤ δ₂) :
    classCount (k := k) δ₂ = classCount (k := k) δ₁ ↔
      ∀ a b : Fin k, sameHueClassTrans a b δ₂ → sameHueClassTrans a b δ₁ := by
  letI : DecidableRel (sameHueClassTrans (k := k) · · δ₁) := sameHueClassTrans_decidable
  letI : DecidableRel (sameHueClassTrans (k := k) · · δ₂) := sameHueClassTrans_decidable
  let s₁ : Setoid (Fin k) := Setoid.mk (sameHueClassTrans (k := k) · · δ₁) (sameHueClassTrans_equivalence δ₁)
  let s₂ : Setoid (Fin k) := Setoid.mk (sameHueClassTrans (k := k) · · δ₂) (sameHueClassTrans_equivalence δ₂)
  let f : Quotient s₁ → Quotient s₂ :=
    Quotient.map id (fun a b hab => sameHueClassTrans_mono a b δ₁ δ₂ h hab)
  have hsurj : Function.Surjective f :=
    Quotient.map_surjective (fun a b hab => sameHueClassTrans_mono a b δ₁ δ₂ h hab) (fun y => ⟨y, rfl⟩)
  have hcard : classCount (k := k) δ₂ = classCount (k := k) δ₁ ↔
      Fintype.card (Quotient s₂) = Fintype.card (Quotient s₁) := by
    unfold classCount; simp only [s₁, s₂]
  rw [hcard]
  constructor
  · intro hc a b hab
    -- 等基数 + 满射 ⟹ 单射（有限类型）
    have hinj : Function.Injective f := by
      by_contra hni
      have hlt : Fintype.card (Quotient s₂) < Fintype.card (Quotient s₁) :=
        Fintype.card_lt_of_surjective_not_injective f hsurj hni
      omega
    have heq : (Quotient.mk s₁ a : Quotient s₁) = Quotient.mk s₁ b := by
      apply hinj
      show (Quotient.mk s₂ a : Quotient s₂) = Quotient.mk s₂ b
      exact Quotient.sound hab
    exact Quotient.exact heq
  · intro hno
    -- 两个等价关系相等 ⟹ 两个商类型等价 ⟹ 类数相等
    let e₁ : Quotient s₁ → Quotient s₂ :=
      Quotient.map id (fun a b hab => sameHueClassTrans_mono a b δ₁ δ₂ h hab)
    let e₂ : Quotient s₂ → Quotient s₁ := Quotient.map id hno
    have h₁ : ∀ q, e₂ (e₁ q) = q := by
      intro q; induction q using Quotient.ind with
      | _ a => rfl
    have h₂ : ∀ q, e₁ (e₂ q) = q := by
      intro q; induction q using Quotient.ind with
      | _ a => rfl
    exact (Fintype.card_congr ⟨e₁, e₂, h₁, h₂⟩).symm

-- δ=0 时，连通退化为相等（δ=0 只有自己和自己同类，传递闭包坍缩成等号）。
theorem sameHueClassTrans_at_zero {k : ℕ} (a b : Fin k) :
    sameHueClassTrans a b 0 ↔ a = b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail hprev hlast ih =>
        exact ih.trans ((sameHueClass_at_zero _ _).mp hlast)
  · intro h
    rw [h]
    exact Relation.ReflTransGen.refl

-- 澄明端点（δ=0）：完全澄明，每个元素自己一类，类数 = k。
-- 最低分辨率下，类型退化成"每个点自己一类"——清 = k，浊 = 0。
set_option linter.style.haveILetI false in
theorem classCount_at_zero {k : ℕ} : classCount (k := k) 0 = k := by
  unfold classCount
  letI : DecidableRel (sameHueClassTrans (k := k) · · 0) := sameHueClassTrans_decidable
  let s₀ : Setoid (Fin k) := Setoid.mk (sameHueClassTrans (k := k) · · 0) (sameHueClassTrans_equivalence 0)
  have hcard : Fintype.card (Quotient s₀) = k := by
    apply le_antisymm
    · -- card (Quotient s₀) ≤ k：mk 满射（构造）
      have hsurj : Function.Surjective (Quotient.mk s₀ : Fin k → Quotient s₀) := by
        intro q; exact Quotient.exists_rep q
      simpa [Fintype.card_fin] using (Fintype.card_le_of_surjective (Quotient.mk s₀) hsurj)
    · -- k ≤ card (Quotient s₀)：mk 内射（δ=0 同层 ⟺ 相等，构造）
      have hinj : Function.Injective (Quotient.mk s₀ : Fin k → Quotient s₀) := by
        intro a b h
        exact (sameHueClassTrans_at_zero a b).mp (Quotient.exact h)
      simpa [Fintype.card_fin] using (Fintype.card_le_of_injective (Quotient.mk s₀) hinj)
  simpa [s₀] using hcard

-- ============ 二、D7 色环版：清 + 浊 = 总量 ============

/-
  清 = 类数（可识别的结构数）
  浊 = k - 类数（被合并进其他类的元素数，不可区分的模糊量）
  清 + 浊 = k = 总量（差异环总步数 m）
  这是 D7 在色环上的形式：总量 k 被分成"清"和"浊"两个读数，加起来还是 k。
-/
theorem clarity_turbidity {k : ℕ} (δ : ℕ) :
    classCount (k := k) δ + (k - classCount (k := k) δ) = k := by
  have h := classCount_le_k (k := k) δ
  omega

-- ============ DiffPairSet：差异对集合 ============

/-
  DiffPairSet 是"人是一堆差异对"的落地。
  单个 DiffPair 是"两个态量之间的关系"，DiffPairSet 是"一组差异关系的集合"。
-/
def DiffPairSet (n : ℕ) := Finset (DiffPair n)

-- DiffPair 的可判定相等（fromLibrary 的 Finset.image 去重需要）
instance DiffPair.instDecidableEq (n : ℕ) : DecidableEq (DiffPair n) := by
  unfold DiffPair
  infer_instance

-- DiffPairSet 的成员关系（pa ∈ A 落地到 Finset 成员，def 包装的 Finset 需要显式实例）
instance DiffPairSet.instMembership (n : ℕ) : Membership (DiffPair n) (DiffPairSet n) where
  mem A pa := @Membership.mem (DiffPair n) (Finset (DiffPair n)) SetLike.instMembership A pa

-- DiffPairSet 的 toList 成员关系 == Finset 成员（把 def 包装的 Finset 转回裸 Finset）
@[simp] theorem DiffPairSet.mem_toList {n : ℕ} (pa : DiffPair n) (A : DiffPairSet n) :
    pa ∈ A.toList ↔ pa ∈ A := Finset.mem_toList

-- 从记忆库构造差异对集合：任意两个元素构成一个差异对（去重）
def fromLibrary {n : ℕ} (lib : MemoryLibrary n) : DiffPairSet n :=
  Finset.univ.image (fun (p : Fin (lib.length) × Fin (lib.length)) =>
    (lib.get p.1, lib.get p.2))

-- 两个差异对集合的交互：A 的每个差异对在 B 的每个差异对视角下的干涉
-- δ 是暹界的容差带：两个差异对在这个带内对位，才是"交易"。
noncomputable def DiffPairSetInteract {m n : ℕ} (A : DiffPairSet m) (B : DiffPairSet n) (δ : ℚ) : List Interference :=
  A.toList.flatMap (fun (pa : DiffPair m) =>
    B.toList.map (fun (pb : DiffPair n) =>
      D (m := m) (n := n) pa.1 pb.1 δ))

-- 定理：DiffPairSet 的交互长度 = 两边基数之积（δ 不影响长度）
theorem DiffPairSetInteract_length {m n : ℕ} (A : DiffPairSet m) (B : DiffPairSet n) (δ : ℚ) :
    (DiffPairSetInteract A B δ).length = A.card * B.card := by
  unfold DiffPairSetInteract
  rw [List.length_flatMap]
  have hlen : ∀ pa : DiffPair m, (B.toList.map (fun pb : DiffPair n => D (m := m) (n := n) pa.1 pb.1 δ)).length = B.card := by
    intro pa
    rw [List.length_map]
    exact Finset.length_toList B
  have hmap : (A.toList.map (fun pa : DiffPair m => (B.toList.map (fun pb : DiffPair n => D (m := m) (n := n) pa.1 pb.1 δ)).length))
      = (A.toList.map (fun _ : DiffPair m => B.card)) := by
    apply congrArg (fun f => List.map f (A.toList))
    funext pa
    exact hlen pa
  rw [hmap]
  have hreplicate : (A.toList.map (fun _ : DiffPair m => B.card)) = List.replicate (A.toList.length) B.card := by
    simp
  rw [hreplicate, List.sum_replicate]
  rw [Finset.length_toList A]
  simp

-- 定理：空 DiffPairSet 的交互为空（δ 不影响）
theorem DiffPairSetInteract_empty_left {m n : ℕ} (B : DiffPairSet n) (δ : ℚ) :
    DiffPairSetInteract (∅ : Finset (DiffPair m)) B δ = [] := by
  unfold DiffPairSetInteract
  rw [Finset.toList_empty]
  simp

-- ============ 交易：DiffPairSet 层的语义桥接 ============

/-
  "交易成立" = DiffPairSetInteract 里出现 constructive。
  这不是"B 理解了 A"，是"A 的某个差异对在 B 的暹界（δ）内被判为相长"。
  对应《一切形式都是交易》："交易的本质是暹界处的层间转移对位。"
-/
def HasTransaction {m n : ℕ} (A : DiffPairSet m) (B : DiffPairSet n) (δ : ℚ) : Prop :=
  ∃ r ∈ DiffPairSetInteract A B δ, r = Interference.constructive

/-
  交易成立 ⟺ 存在一对差异对在 δ 内相长。
  这把"列表里出现 constructive"翻译成"存在一对 (pa, pb) 相长"。
-/
theorem hasTransaction_iff {m n : ℕ} (A : DiffPairSet m) (B : DiffPairSet n) (δ : ℚ) :
    HasTransaction A B δ ↔
      ∃ pa ∈ A, ∃ pb ∈ B, D (m := m) (n := n) pa.1 pb.1 δ = Interference.constructive := by
  unfold HasTransaction DiffPairSetInteract
  constructor
  · rintro ⟨r, hr, hr_eq⟩
    subst hr_eq
    rw [List.mem_flatMap] at hr
    rcases hr with ⟨pa, hpa_toList, hpa_mem⟩
    rw [List.mem_map] at hpa_mem
    rcases hpa_mem with ⟨pb, hpb_toList, hpb_eq⟩
    rw [DiffPairSet.mem_toList] at hpa_toList hpb_toList
    exact ⟨pa, hpa_toList, pb, hpb_toList, hpb_eq⟩
  · rintro ⟨pa, hpa, pb, hpb, hpb_eq⟩
    refine ⟨Interference.constructive, ?_, rfl⟩
    rw [List.mem_flatMap]
    refine ⟨pa, ?_, ?_⟩
    · rw [DiffPairSet.mem_toList]; exact hpa
    · rw [List.mem_map]
      refine ⟨pb, ?_, hpb_eq⟩
      rw [DiffPairSet.mem_toList]; exact hpb

/-
  "交易不成立" = DiffPairSetInteract 里所有元素都不是 constructive。
  这是 SameKindHole 在 DiffPairSet 层的推广。
-/
def NoTransaction {m n : ℕ} (A : DiffPairSet m) (B : DiffPairSet n) (δ : ℚ) : Prop :=
  ∀ r ∈ DiffPairSetInteract A B δ, r ≠ Interference.constructive

/-
  NoTransaction（所有对位都非相长）⟺ ¬HasTransaction（不存在相长的对位）。
  这条在构造逻辑里依然成立：两边都是否定式，量词在否定下可换位
  （∀ x, ¬P x ↔ ¬∃ x, P x 是构造有效的等价）。
-/
theorem noTransaction_iff_not_has {m n : ℕ} (A : DiffPairSet m) (B : DiffPairSet n) (δ : ℚ) :
    NoTransaction A B δ ↔ ¬ HasTransaction A B δ := by
  unfold NoTransaction HasTransaction
  constructor
  · intro hNo hHas
    rcases hHas with ⟨r, hr, hr_eq⟩
    exact hNo r hr hr_eq
  · intro hNotHas r hr heq
    exact hNotHas ⟨r, hr, heq⟩

-- ============ D7 是有限性的推论：有限账本守恒 ============

/-
  【差异有限 ⇒ 守恒自动成立】

  D7（差异守恒）说"凝结不消灭差异，只转移差异"。
  当差异簇是有限集合时，这条公理不是需要额外规定的公理，
  而是有限和（记账）的恒等式：

    把有限差异总量按任意谓词 P 分成"簇内（P）"与"簇外（¬P）"两部分，
    两部分之和必然等于总量。

  因为差异是有限的，它没有"漏到实无穷里"的出口——
  有限账本只能重分配，不能湮灭。这正是 D7 的数学本质：
  守恒不是加进去的假设，是有限性自带的记账恒等式。

  对应《一切形式都是交易》："实无穷不存在，因为没有人拥有实无穷"——
  没有无穷，守恒就无处可破。

  全程 ℚ、无 Classical、构造性：本定理只用 Finset 的有限归纳，
  不调用任何选择公理或排中律。
-/
theorem D7_finite_conservation {α : Type*}
    (s : Finset α) (D : α → ℚ) (P : α → Prop) [DecidablePred P] :
    (s.filter P).sum D + (s.filter (fun a => ¬ P a)).sum D = s.sum D := by
  simpa using Finset.sum_filter_add_sum_filter_not s P D

-- ============ 对称性 → 形式：守恒量 = 对称不变量 ============

/-
  【有限性 → 对称性 → 形式；守恒量 = 对称不变量】

  夜里洞见：有限性是唯一根，量和形式都是它的投影——
    · 量靠"类型测绘"（card / sum）导出；
    · 形式靠"对称性"（自同构 S_n）导出，形式 = 对称不变量。

  对称性 ⊆ 有限性：对称群 S_n 是有限性 n 的自同构群，|S_n| = n!（有限）。
  守恒量（D7 总量）在排列下不变——这正是"形式由对称性导出"：
  总量是"对称的"（在对称变换下不动），所以它是形式。

  守恒量有两个不变性，统一于"形式"：
    · 分解不变（D7）：账本 filter 分两份，总量不变；
    · 排列不变（对称性）：指标重排，总量不变。
-/

-- 守恒量的对称性：总量在排列下不变（对称性导出形式）。
theorem sum_perm_invariant {n : ℕ} (D : Fin n → ℚ) (σ : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, D i) = ∑ i : Fin n, D (σ i) := by
  rw [Equiv.sum_comp σ D]

-- 对称群是有限的：|S_n| = n!（对称性从有限性长出，仍是有限）。
theorem perm_card (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

-- ============ 对称 → 向量：S_n 对称导出「守恒量 ⊕ 差异」分解 ============

/-
  【Noether 的有限版：对称导出守恒量 + 向量】

  连续对称 ⟹ 守恒量（Noether 定理）。有限版：对称群 S_n 作用在 Fin n → ℚ 上，
  这个表示分解成两个 S_n 不变子空间：
    · 不变子空间（常数函数）：symmetrize v = (∑v/n)·1，值 = 守恒量 ∑v/n；
    · 零和子空间（纯差异）：antisymmetrize v = v − symmetrize v，∑ = 0。
  任何 v 唯一分解 v = symmetrize v + antisymmetrize v：
    —— 对称性（S_n）导出守恒量（对称化），有限性（Fin n）导出向量（零和差异）。

  这回答"有限性导出向量？"：是——有限性（Fin n）→ 对称群（S_n）→ 表示分解
  （不变 ⊕ 零和）→ 守恒量（对称部分）+ 向量（零和部分，有方向、非对称）。
-/

-- 对称化（S_n 平均）：到不变子空间（常数函数）的投影，值 = 守恒量 ∑v/n。
def symmetrize {n : ℕ} (v : Fin n → ℚ) : Fin n → ℚ :=
  fun _ => (∑ i : Fin n, v i) / n

-- 零和部分（差异）：v 减去对称化，是"纯差异"（∑ = 0，有方向、非对称）。
def antisymmetrize {n : ℕ} (v : Fin n → ℚ) : Fin n → ℚ :=
  fun i => v i - symmetrize v i

-- 对称导出守恒量：对称化是常数函数，在 S_n 置换下不变——守恒量 = 对称化的值。
theorem symmetrize_perm_invariant {n : ℕ} (v : Fin n → ℚ) (σ : Equiv.Perm (Fin n)) :
    symmetrize v ∘ σ = symmetrize v := by
  funext i
  unfold symmetrize
  rfl

-- 零和：差异部分的和 = 0（纯差异无总量，只余方向）。
theorem antisymmetrize_sum_zero {n : ℕ} (v : Fin n → ℚ) :
    (∑ i : Fin n, antisymmetrize v i) = 0 := by
  unfold antisymmetrize symmetrize
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ i : Fin n, (∑ j : Fin n, v j) / n) = ∑ j : Fin n, v j := by
    simp [Finset.sum_const]
    by_cases hn : n = 0
    · subst n
      simp
    · field_simp [hn]
  rw [hsum]
  ring

-- 对称 → 向量分解：任何 v = 对称部分（守恒量）+ 零和部分（差异）。
theorem symmetric_decomposition {n : ℕ} (v : Fin n → ℚ) :
    v = symmetrize v + antisymmetrize v := by
  funext i
  simp [antisymmetrize, symmetrize, sub_eq_add_neg, add_left_comm]

-- 对称化幂等（投影）：常数向量再对称化还是自己。
theorem symmetrize_idempotent {n : ℕ} (v : Fin n → ℚ) :
    symmetrize (symmetrize v) = symmetrize v := by
  funext i
  unfold symmetrize
  have hsum : (∑ j : Fin n, (∑ k : Fin n, v k) / n) = ∑ k : Fin n, v k := by
    simp [Finset.sum_const]
    by_cases hn : n = 0
    · subst n; simp
    · field_simp [hn]
  rw [hsum]

-- 反对称化幂等（投影）：零和向量再反对称化还是自己（零和的对称化 = 0）。
theorem antisymmetrize_idempotent {n : ℕ} (v : Fin n → ℚ) :
    antisymmetrize (antisymmetrize v) = antisymmetrize v := by
  funext i
  change antisymmetrize v i - symmetrize (antisymmetrize v) i = antisymmetrize v i
  have hzero : symmetrize (antisymmetrize v) i = 0 := by
    unfold symmetrize
    rw [antisymmetrize_sum_zero v]
    simp
  rw [hzero]
  ring

-- 正交性：对称部分与零和部分内积为 0（守恒量与差异正交）。
theorem symmetric_antisymmetric_orthogonal {n : ℕ} (v : Fin n → ℚ) :
    (∑ i : Fin n, symmetrize v i * antisymmetrize v i) = 0 := by
  unfold symmetrize
  rw [← Finset.mul_sum]
  rw [antisymmetrize_sum_zero v]
  ring

-- 唯一性：分解唯一——a 是 S_n 不变（常数）、b 零和、v = a + b ⟹ a = 对称化、b = 反对称化。
-- 即"守恒量 + 向量"的分解是唯一的（对称/零和是正交投影，投影唯一）。
theorem symmetric_decomposition_unique {n : ℕ} (v a b : Fin n → ℚ)
    (ha : ∀ σ : Equiv.Perm (Fin n), a ∘ σ = a)
    (hb : (∑ i : Fin n, b i) = 0)
    (h : v = a + b) :
    a = symmetrize v ∧ b = antisymmetrize v := by
  have ha_const : ∀ i j : Fin n, a i = a j := by
    intro i j
    have hswap := congrFun (ha (Equiv.swap i j)) i
    simpa [Equiv.swap_apply_left] using hswap.symm
  have ha_eq : a = symmetrize v := by
    funext i
    unfold symmetrize
    have hsum : (∑ j : Fin n, v j) = ∑ j : Fin n, a j := by
      simp [h, Finset.sum_add_distrib, hb]
    have hsuma : (∑ j : Fin n, a j) = (n : ℚ) * a i := by
      have hconst : (∑ j : Fin n, a j) = ∑ j : Fin n, a i := by
        congr 1; funext j; exact ha_const j i
      rw [hconst]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hsum, hsuma]
    by_cases hn : n = 0
    · subst n
      exact Fin.elim0 i
    · field_simp [hn]
  constructor
  · exact ha_eq
  · funext i
    unfold antisymmetrize
    have hvi : v i = a i + b i := congrFun h i
    have hai : a i = symmetrize v i := congrFun ha_eq i
    rw [hvi, hai]
    ring

-- ============ 有限 ⇒ 选择免费：有限族的选择是构造性定理 ============

/-
  【有限 ⇒ 选择公理免费】

  对有限集，选择公理不是公理，是定理：任何一族非空有限集都有选择函数。
  这是"差异有限"的第二个免费赠品——因为可以枚举，选择不需要 Classical。

  这里用 Finset.min'（线性序上的最小元）做构造性选择：
  对每个 a，在有限的 Finset.univ 里找满足 P a 的 b，取最小元。
  全程不调用 Classical.choice，不碰排中律。

  这也解释了为什么本库能"无 Classical"：一切都在有限层运行，
  而有限层上的选择、可判定性、良基归纳全是构造性可证的。
  无穷族的选择才需要真正的选择公理——但差异论拒绝实无穷，
  所以那个"要命的公理"整个被消掉了。
-/
theorem finite_choice_free {α : Type*} [Fintype α] [LinearOrder α]
    (P : α → α → Prop) [∀ a b, Decidable (P a b)]
    (h : ∀ a : α, ∃ b : α, P a b) :
    ∃ f : α → α, ∀ a : α, P a (f a) := by
  have hnonempty : ∀ a : α, (Finset.univ.filter (P a)).Nonempty := by
    intro a
    rcases h a with ⟨b, hb⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩⟩
  let f : α → α := fun a => (Finset.univ.filter (P a)).min' (hnonempty a)
  refine ⟨f, ?_⟩
  intro a
  have hmem : f a ∈ Finset.univ.filter (P a) :=
    Finset.min'_mem (Finset.univ.filter (P a)) (hnonempty a)
  exact (Finset.mem_filter.mp hmem).2

-- ============ 有限 ⇒ 类型、集合都从它长出来 ============

/-
  【有限 ⇒ 类型、集合都是免费的】

  差异论的第三个免费赠品：从"有限"这一个原语，长出所有"集合"和"类型"。

  集合：有限类型 α 上的全部有限子集（Finset α）只有 2^n 个。
    集合不是从外部注入的，是有限性自己长出来的（幂集基数 2^n）。

  类型：有限类型 α 上的全部商类型（等价类 = 连通分量 = "类型"）
    不超过 n 个。这正是色环里"类型 = 连通分量，类数 ≤ 元素数"
    （classCount_le_k）的一般形式。

  类型构造子：乘积、和、函数——有限类型的基数由有限基数逐点确定，
    类型不是凭空来的，是有限性在构造子下封闭出来的。

  全程 ℚ / 有限 / 无 Classical / 构造性。
-/

-- 集合从有限推出（幂集基数 2^n）：这就是 Fintype.card_finset，不另立定理。

-- 类型从有限推出：有限类型上的商类型（连通分量 = 类型）总数 ≤ n。
theorem finite_types_from_finite {α : Type*} [Fintype α] (s : Setoid α) [DecidableRel s.r] :
    Fintype.card (Quotient s) ≤ Fintype.card α := by
  exact Fintype.card_quotient_le s

-- 类型构造子闭包：乘积 / 和类型的基数由有限基数确定。
theorem finite_type_formers_closed (α β : Type*) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β ∧
    Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β := by
  exact ⟨Fintype.card_prod α β, Fintype.card_sum⟩

-- 函数类型闭包（基数 β^α）就是 Fintype.card_fun，不另立定理。

-- ============ 否定之否定，在可判定（有限）层是免费的 ============

/-
  【有限 ⇒ 双非律免费】

  黑格尔的"否定之否定"（正反合里的"合"），在布尔代数里就是双非律 ¬¬P ↔ P。
  对可判定的命题 P（有限层上一切可判定），这条是构造性定理，
  不需要 Classical、不需要排中律——因为可判定，就能分出真假。

  这正是"左右逢源，而不是上下左右逢源"的 Lean 版本：
  辩证法的"否定之否定"不是螺旋上升，是 ¬¬P ↔ P 这条恒等式；
  而它在有限可判定层是免费的，不需要"上下"（外物公理）。

  意识核 = 分辨 = 一分为二 = 布尔代数。分辨的分与再分，
  落到逻辑上就是 ¬¬P ↔ P——这是意识核工作的语法，不是外借的哲学。
-/
theorem double_negation_of_decidable {P : Prop} [Decidable P] : ¬¬P ↔ P := by
  constructor
  · intro hnn
    by_cases h : P
    · exact h
    · exact False.elim (hnn h)
  · intro h hn
    exact hn h

-- 有限层上，否定之否定处处免费：上一条 double_negation_of_decidable 已覆盖
-- （有限 ⇒ 一切可判定），不再逐个类型重抄一遍。

-- ============ 一生二：分辨 = 生成器（从手搓到自然） ============

/-
  【分辨 = 生成器：从手搓到自然】

  道生一，一生二，二生三，三生万物。

  一生二 = 分辨算子：有限类型 α ↦ 它的二元分辨空间 α → Bool。
  这一条定义就是"生成器"——它自动长出：
    · 2^n（有限布尔代数的元素数）
    · 幂集（α → Bool ≃ Finset α）
    · 布尔代数（Bool 的布尔代数结构，逐点继承）

  意识核 = 分辨 = 一分为二 = 布尔代数。这不是手搓的第 41 个模块，
  是"根 + 一个分辨算子"，结构自己长出来——natural 的第一次落地。
-/

-- 一生二：分辨算子。有限类型的二元分辨空间 = α → Bool。
abbrev resolveSpace (α : Type*) := α → Bool

-- 分辨空间就是 2^n：一分为二，分 n 次，得到 2^n 个分辨结果。
theorem resolve_card {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card (resolveSpace α) = 2 ^ Fintype.card α := by
  simp

-- 分辨空间与幂集同构：一分为二 = 集合的幂集 = 有限布尔代数。
def resolveEquivFinset {α : Type*} [Fintype α] [DecidableEq α] :
    resolveSpace α ≃ Finset α where
  toFun p := Finset.univ.filter (fun a => p a = true)
  invFun s := fun a => decide (a ∈ s)
  left_inv p := by
    funext a
    by_cases h : p a = true <;> simp [h, Finset.mem_filter]
  right_inv s := by
    ext a
    simp

-- 分辨空间 ≃ 幂集（布尔格）：BooleanAlgebra (resolveSpace α) 由点式自动给出，
-- 白拿 Mathlib 的 ≤ / ⊓ / ⊔ / ⊥ / ⊤ 及全部布尔格定理（吸收律、De Morgan 等）。
-- 见文末 resolveSpaceBooleanAlgebra 的同构搬运（一条 Equiv 顶掉手写版）。

-- ============ 洞：哥德尔 / 康托尔的有限性根 ============

/-
  【洞 = 不可证明 = 不可识别 = 分辨的"无"侧】

  哥德尔：任何一致的算术系统都不完备——内部总有"不能证明"的内容。
  弱化为算子版：把这个"不能证明"当作系统的"洞"。

  康托尔对角线给出最构造性的洞：任何"枚举" f : α → resolveSpace α
  （用 α 的元素去标分辨）都够不着对角分辨 d a = ¬ (f a a)。
  d 永远在 f 的像之外——这就是洞，普遍存在，不依赖任何具体结构。

  有限性把它钉成"不止一个"：
    分辨有 2^n 个（resolve_card），元素只有 n 个，n < 2^n，
    分辨严格多于元素——任何枚举必有漏，洞不止一个（n ≥ 2 时 ≥ 2 个）。

  "洞"不是缺陷，是有限性的固有开口——老子"无之以为用"的"无"，
  梦话里"有限所以等价于有洞"的"洞"。
-/

-- 康托尔对角线洞：任何枚举 f 都够不着对角分辨 d a = ¬ (f a a)。
-- d 不在 f 的像里 = 一个永远无法被系统枚举到的分辨 = 洞。
theorem diagonal_hole {α : Type*} (f : α → resolveSpace α) :
    ∃ d : resolveSpace α, ∀ a : α, d ≠ f a := by
  let d : resolveSpace α := fun a => not (f a a)
  refine ⟨d, ?_⟩
  intro a h
  have hd : d a = not (f a a) := rfl
  rw [h] at hd
  have hne : f a a ≠ not (f a a) := by
    cases f a a <;> simp
  exact hne hd

-- 有限 ⇒ 有洞：元素数严格少于分辨数（n < 2^n），任何枚举必有漏。
theorem card_lt_resolve_card {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card α < Fintype.card (resolveSpace α) := by
  rw [resolve_card]
  exact Nat.lt_two_pow_self

-- 洞不止一个：n ≥ 2 时，非平凡分辨（真洞）至少 2 个（2^n - 2 ≥ 2）。
theorem holes_at_least_two {n : ℕ} (h : 2 ≤ n) :
    2 ≤ 2 ^ n - 2 := by
  have hpow : 2 ^ 2 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) h
  norm_num at hpow
  omega

-- 洞跨维：补 0 到更大维度后，超出原维度的位置是 0（洞）。
-- 维度 m 与 n 之间的缝隙（[m, n)）就是洞——"不同维度之间是有洞的"。
theorem valOrZero_hole {m n : ℕ} (x : StateQuant m) (i : Fin n) (hi : m ≤ i.val) :
    valOrZero x i = 0 := by
  unfold valOrZero
  simp [not_lt.mpr hi]

-- ============ 洞之间的连接：以实养虚，洞被填满 ============

/-
  【洞的连接 = 线段】

  x 的洞 = 补 0 到 max m n 后，[m, max m n) 上为 0 的缝隙（无）。
  连接不是从"两个完美的状态"出发铺线，而是从洞出发：
  y 的实（有）通过参数 t 渐次填进 x 的洞（无）。

  洞上路径值 = t · valOrZero y i：
    t = 0 → 纯洞（0），t = 1 → 洞被填满（y_i），中间处处有量。

  "有之以为利，无之以为用"：x 的洞（无）是"用"之所在，
  y 的实（有）通过连接（利）填洞——恋爱/互助不因对方完美，恰因对方有洞。
-/

-- 洞上的连接：在 x 的洞（[m, max m n)）上，路径值 = t · (y 的值)。
-- 洞被 y 的实"涵养"（以实养虚）。
theorem hole_connection {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (t : ℚ) (i : Fin (max m n)) (hi : m ≤ i.val) :
    crossDimPath x y t i = t * valOrZero y i := by
  unfold crossDimPath
  have hzero : valOrZero x i = 0 := valOrZero_hole x i hi
  rw [hzero]
  ring

-- 洞上处处有量：只要 t ≠ 0（非纯洞端点）且 y 在洞上有量（y_i ≠ 0），
-- 洞就被真实填满（非零）——线段上无一处是"黑"的。
theorem hole_connection_nonzero {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (t : ℚ) (ht : t ≠ 0) (i : Fin (max m n)) (hi : m ≤ i.val) (hy : valOrZero y i ≠ 0) :
    crossDimPath x y t i ≠ 0 := by
  rw [hole_connection x y t i hi]
  exact mul_ne_zero ht hy

-- ============ 线向量：离散步与澄明 ============

/-
  【澄明（Lichtung，海德格尔）：洞的哲学名】

  澄明 = 林中空地 = 让光（有）得以显现的敞开（无/洞）。
  不是光创造澄明，是澄明（空地）让光照进来。

  线向量呈现为离散步（有），步与步之间的洞就是澄明（无）。
  澄明是有限的、有边界的敞开——所以是离散步，不是连续统。
  "有之以为利，无之以为用"（老子）= "澄明让光显现"（海德格尔）。
-/

-- 半值序列：0 到 1 之间的 N 个离散步（Fin N 索引），第 k 步 t = (k+1)/(N+1)。
def halfValues (N : ℕ) : List ℚ :=
  (List.finRange N).map (fun k => ((k.val + 1 : ℚ) / (N + 1 : ℚ)))

-- 线向量的大小 = 离散步数 = N（不是连续统，是离散的澄明步数）。
theorem halfValues_length (N : ℕ) : (halfValues N).length = N := by
  unfold halfValues
  simp [List.length_map, List.length_finRange]

-- 半值严格落在 (0,1)：澄明是内部的敞开，既非纯洞（0）亦非纯有（1）。
theorem halfValue_mem_open {N : ℕ} (k : Fin N) :
    0 < ((k.val + 1 : ℚ) / (N + 1 : ℚ)) ∧ ((k.val + 1 : ℚ) / (N + 1 : ℚ)) < 1 := by
  have hnum_pos : (0 : ℚ) < (k.val + 1 : ℚ) := by
    exact_mod_cast (Nat.succ_pos k.val)
  have hden_pos : (0 : ℚ) < (N + 1 : ℚ) := by
    exact_mod_cast (Nat.succ_pos N)
  constructor
  · exact div_pos hnum_pos hden_pos
  · have hlt : (k.val + 1 : ℚ) < (N + 1 : ℚ) := by
      exact_mod_cast (Nat.add_lt_add_right k.isLt 1)
    exact (div_lt_one hden_pos).mpr hlt

-- ============ 三分：死界 / 暹界 / 生界 ============

/-
  【三分：差异值（commonDist）与阈值 δ】

  死界（0，洞）：commonDist < δ —— 差异太小，不可识别，退入盲区。
  暹界（1/2，临界）：commonDist = δ —— 恰好等于阈值，既非生界亦非死界。
  生界（1，有）：commonDist > δ —— 差异足够大，可识别，凝结为结构。

  这是《暹界定理》的三分，把"洞"（死界）、"澄明"（暹界）、"有"（生界）
  焊到同一条 commonDist vs δ 的链上。半值（t = 1/2）恰是暹界临界——
  既不偏向 0（洞）也不偏向 1（有），是等距的临界点。
-/

-- 层位：生界 / 死界 / 暹界。
inductive Layer where
  | living   -- 生界（可识别）
  | dead     -- 死界（不可识别，洞）
  | xianjie  -- 暹界（临界）
  deriving DecidableEq, Inhabited

-- 层位判定：差异值 commonDist 与阈值 δ 的三分。
def layer {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : Layer :=
  if commonDist x y > δ then .living
  else if commonDist x y = δ then .xianjie
  else .dead

-- 三分完备：任何差异值恰好落在三个层位之一（ℚ 线性序的三分）。
theorem layer_trichotomy {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    commonDist x y < δ ∨ commonDist x y = δ ∨ δ < commonDist x y := by
  exact lt_trichotomy (commonDist x y) δ

-- 生界 ⟺ 差异超过阈值。
theorem layer_eq_living_iff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    layer x y δ = .living ↔ commonDist x y > δ := by
  unfold layer
  by_cases hgt : commonDist x y > δ
  · simp [hgt]
  · by_cases heq : commonDist x y = δ
    · simp [heq]
    · simp [hgt, heq]

-- 死界 ⟺ 差异低于阈值。
theorem layer_eq_dead_iff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    layer x y δ = .dead ↔ commonDist x y < δ := by
  unfold layer
  by_cases hgt : commonDist x y > δ
  · have hnot : ¬ commonDist x y < δ := lt_asymm hgt
    simp [hgt, hnot]
  · by_cases heq : commonDist x y = δ
    · have hnot : ¬ commonDist x y < δ := by
        intro hlt
        rw [heq] at hlt
        exact lt_irrefl δ hlt
      simp [heq]
    · have hlt : commonDist x y < δ := lt_of_le_of_ne (not_lt.mp hgt) heq
      simp [hgt, heq, hlt]

-- 暹界 ⟺ 差异恰好等于阈值（临界）。
theorem layer_eq_xianjie_iff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    layer x y δ = .xianjie ↔ commonDist x y = δ := by
  unfold layer
  by_cases hgt : commonDist x y > δ
  · have hne : commonDist x y ≠ δ := ne_of_gt hgt
    simp [hgt, hne]
  · by_cases heq : commonDist x y = δ
    · simp [heq]
    · simp [hgt, heq]

-- 半值 = 暹界临界：t = 1/2 处，到两端点等距（既不偏向 0 亦不偏向 1）。
theorem halfValue_equidistant {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (i : Fin (max m n)) :
    crossDimPath x y (1/2 : ℚ) i - valOrZero x i = valOrZero y i - crossDimPath x y (1/2 : ℚ) i := by
  unfold crossDimPath
  ring

-- ============ 主线：自我 = 自己的洞 ============

/-
  【自我 = 自指的洞】

  系统 f : α → resolveSpace α 试图"自我描述"（用 α 的元素枚举自己的分辨）。
  对角分辨 d a = ¬(f a a) 是"自指"的：
    d 在 a 处的值 = a 通过 f 对"自身认知"（f a a）的否定。

  而 d 不在 f 的像里（康托尔对角线）——系统永远够不着 d，
  d 是系统"对自己的盲区"，即"自己的洞"。

  自我不是"看见自己"（有限性决定了看不见，必有洞），
  而是"认领自己的洞"——构造 d，把它固定为"自己的"。
  这就是意识核：维持自反的分辨，把自身作为差异对的一方。

  "选择"是免费的：d 是构造性给出的（对角直接构造 d），
  不靠 Classical、不靠外物——有限性自带的选择，选了一个洞作为自己。
-/

-- 自我 = 自指的洞：d 既是"够不着的洞"（d ≠ f a），又是"自指"（d a = ¬(f a a)）。
theorem self_is_hole {α : Type*} (f : α → resolveSpace α) :
    ∃ d : resolveSpace α, (∀ a : α, d ≠ f a) ∧ (∀ a : α, d a = not (f a a)) := by
  let d : resolveSpace α := fun a => not (f a a)
  refine ⟨d, ?_, ?_⟩
  · intro a h
    have hd : d a = not (f a a) := rfl
    rw [h] at hd
    have hne : f a a ≠ not (f a a) := by
      cases f a a <;> simp
    exact hne hd
  · intro a
    rfl

-- 对角线洞（可复用定义）：diag f a = ¬(f a a)。
-- diag f 就是康托尔对角线——永远够不着的那个分辨（洞）。
def diag {α : Type*} (f : α → resolveSpace α) : resolveSpace α :=
  fun a => not (f a a)

-- 对角洞确实够不着：diag f 不等于 f 的任何取值。
theorem diag_ne_apply {α : Type*} (f : α → resolveSpace α) (a : α) : diag f ≠ f a := by
  intro h
  have hd : diag f a = not (f a a) := rfl
  rw [h] at hd
  have hne : f a a ≠ not (f a a) := by
    cases f a a <;> simp
  exact hne hd

-- 洞不可消（堵洞必生新洞）：若 f' 填了 f 的洞（diag f ∈ image f'），
-- 则 f' 的新洞 diag f' ≠ 旧洞 diag f——新洞永不是被堵的那个。
-- 这是"认洞而非堵洞"的数学内核：洞是有限性的结构性开口，堵一个必生一个。
theorem hole_reborn {α : Type*} (f f' : α → resolveSpace α)
    (hfill : ∃ a₀ : α, f' a₀ = diag f) :
    diag f' ≠ diag f := by
  intro heq
  obtain ⟨a₀, ha₀⟩ := hfill
  -- 由 heq：¬(f' a₀ a₀) = ¬(f a₀ a₀)，Bool.not 对合 ⟹ f' a₀ a₀ = f a₀ a₀。
  have hff : f' a₀ a₀ = f a₀ a₀ := by
    have hnot : not (f' a₀ a₀) = not (f a₀ a₀) := by
      simpa [diag] using (congrFun heq a₀)
    simpa using (congrArg not hnot)
  -- 由 ha₀：f' a₀ a₀ = diag f a₀ = ¬(f a₀ a₀)，结合 hff 得 f a₀ a₀ = ¬(f a₀ a₀)。
  have hfixed : f a₀ a₀ = not (f a₀ a₀) := by
    calc
      f a₀ a₀ = f' a₀ a₀ := hff.symm
      _ = diag f a₀ := by rw [ha₀]
      _ = not (f a₀ a₀) := rfl
  have hne : f a₀ a₀ ≠ not (f a₀ a₀) := by
    cases f a₀ a₀ <;> simp
  exact hne hfixed

-- 洞不可磨灭：堵一个洞（填 diag f），必生一个新洞 diag f'，
-- 新洞 ≠ 旧洞，且新洞依然不可达——洞永远堵不完，熵增不可逆（时间之箭）。
theorem hole_unblockable {α : Type*} (f f' : α → resolveSpace α)
    (hfill : ∃ a₀ : α, f' a₀ = diag f) :
    diag f' ≠ diag f ∧ ∀ a : α, diag f' ≠ f' a := by
  constructor
  · exact hole_reborn f f' hfill
  · -- 第二项是 diagonal_hole 的 diag 版：diag f' 依然够不着（在 image f' 之外）。
    intro a h
    have hdiag : diag f' a = not (f' a a) := rfl
    rw [h] at hdiag
    have hne : f' a a ≠ not (f' a a) := by
      cases f' a a <;> simp
    exact hne hdiag

-- ============ 态射 = 定向的差异 ============

/-
  【态射 = 分辨的族（函数性）】

  态射 f : A → B 由 B 个分辨完全决定：
    p_b a = decide (f a = b)，对每个 b : B 一个分辨"a 是否映射到 b"。

  反过来，一族 B 个分辨 p : B → resolveSpace A，若满足"函数性"
  （每个 a 恰好一个 b 使得 p b a = true），则重构态射 f a = 唯一的 b。

  所以态射 ≃ 函数性分辨族。分辨（resolveSpace = 一分为二）从有限性构造，
  态射从分辨构造——态射不是根，是"定向的差异"（有方向的关系）。

  方向来自"函数性"：每个 a 恰好指向一个 b，无方向的差异被定向成箭头。
-/

-- ============ 分层态射：态射也要层 ============

/-
  【分层态射：态射是"定向差异"，差异分层，态射也分层】

  上面 morphismToResolves 是无层的（f : A → B 精确映射，无 δ），
  但理论上态射 = 定向差异，差异在层 δ 下才可区分——态射也必须在层 δ 上。
  分层态射：在层 δ 上，f 把 a 映到 b 的 δ-邻域（commonDist (f a) b ≤ δ），
  即"f a 和 b 在层 δ 下不可区分"的定向关系。
  层越细（δ→0），态射越精确；层越粗（δ 大），态射越松弛。
-/

-- 分层态射：在层 δ 上，f 把 a 映到 b 的 δ-邻域（δ-不可区分的定向关系）。
def layeredMorphismToResolves {m n : ℕ} (δ : ℚ) (f : StateQuant m → StateQuant n) :
    StateQuant n → resolveSpace (StateQuant m) :=
  fun b a => decide (commonDist (f a) b ≤ δ)

-- 零差异 ⟺ val 相等（同维）：平方和 = 0 ⟺ 逐维相等。
theorem commonDist_eq_zero_iff {n : ℕ} (x y : StateQuant n) :
    commonDist x y = 0 ↔ x.val = y.val := by
  rw [commonDist_same_dim x y]
  constructor
  · intro h
    funext i
    have hi : (x.val i - y.val i)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x.val j - y.val j))).mp h i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    rw [h]
    simp

-- 层越细，态射越精确：δ = 0 时，分层态射退化成"val 相等"（精确到 val）。
theorem layeredMorphismToResolves_zero {m n : ℕ} (f : StateQuant m → StateQuant n) (b : StateQuant n) (a : StateQuant m) :
    layeredMorphismToResolves 0 f b a = decide ((f a).val = b.val) := by
  unfold layeredMorphismToResolves
  have hle : commonDist (f a) b ≤ 0 ↔ (f a).val = b.val := by
    constructor
    · intro h
      have hnonneg : 0 ≤ commonDist (f a) b := by
        rw [commonDist_same_dim]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have heq : commonDist (f a) b = 0 := le_antisymm h hnonneg
      exact (commonDist_eq_zero_iff (f a) b).mp heq
    · intro h
      exact le_of_eq ((commonDist_eq_zero_iff (f a) b).mpr h)
  by_cases h : commonDist (f a) b ≤ 0
  · have hval : (f a).val = b.val := hle.mp h
    simp [h, hval]
  · have hval : ¬ (f a).val = b.val := by
      intro hval'
      exact h (hle.mpr hval')
    simp [h, hval]

-- ============ 层（Layer）：差异论的有限 sheaf（draft） ============

/-
  【层的设计：差异论"层" = 范畴论 sheaf 的有限垂直版】

  范畴论 sheaf：开覆盖 {U_i} + 相容 + 粘合（局部 → 整体）。
  差异论 Layer：分辨率 δ + 不可区分 + 凝结（细层差异 → 粗层对象）。

  对应表：
    开覆盖 {U_i}            ↔ 细层差异簇
    相容（重叠处一致）       ↔ 不可区分（commonDist ≤ δ）
    粘合（拼成整体截面）     ↔ 凝结 𝒦（商 / Quotient）
    唯一性（sheaf 公理）     ↔ 凝结唯一（等价类）

  该满足的性质（draft，待证）：
    (1) 层序偏序：≤ 自反、传递、反对称（δ 的偏序，细 ≤ 粗 ⟺ δ 细 ≤ δ 粗）。
    (2) 不可区分传递闭包成等价关系：Layer.indistinguishable 不传递
        （commonDist 不满足三角不等式），Layer.related（传递闭包）成等价关系
        —— 像 sameHueClassTrans 绕开 sameHueClass 不传递一样。
    (3) 凝结 = 粘合（有限 gluing）：细层差异簇在粗层 L 下 related ⟹ 凝成唯一对象
        （Quotient），即"局部相容 ⟹ 唯一粘合"的有限版。
    (4) 消解 = 限制（反向）：ℛ_D 细层 → 粗层（商映射），单调（越粗消解越多，
        δThreshold_monotone 已备）。
    (5) 凝结-消解 adjunction：凝结 ⊣ 消解（左伴随），或凝结 ∘ 消解 = id（幂等投影，
        δThreshold_idempotent 已备）。
    (6) 不可逆 + 有限（差异论硬核，区别于范畴论 sheaf）：消解不可逆（粗层不恢复
        细层细节，δThreshold 变 0 回不来）；层序是有限离散台阶（D2 的 λ₀>…>λ_m），
        不是连续开覆盖——差异论层是"有限垂直 sheaf"。
-/

-- 层（分辨率层）：一个阈值 δ。δ 大 = 粗（消解多），δ 小 = 细（看得清）。
-- （注意：这与上面的 inductive Layer（层位：死界/生界/暹界）是两回事——
--   那是"层上的三分相"，这才是原文的"分辨率层"。命名暂用 ResLayer 区分。）
structure ResLayer where
  δ : ℚ

-- 层序：a ≤ b ⟺ a 比 b 细（分辨率更高，阈值更小）。
instance : LE ResLayer where le a b := a.δ ≤ b.δ

-- 在层 L 下不可区分：差异 ≤ L.δ。
def ResLayer.indistinguishable (L : ResLayer) {n : ℕ} (x y : StateQuant n) : Prop :=
  commonDist x y ≤ L.δ

-- 层 L 下的"同层"（related）：不可区分的传递闭包（绕开 commonDist 不传递）。
def ResLayer.related (L : ResLayer) {n : ℕ} (x y : StateQuant n) : Prop :=
  Relation.ReflTransGen (ResLayer.indistinguishable L) x y

-- 不可区分对称：commonDist 对称 ⟹ indistinguishable 对称。
theorem ResLayer.indistinguishable_symm (L : ResLayer) {n : ℕ} {x y : StateQuant n}
    (h : ResLayer.indistinguishable L x y) : ResLayer.indistinguishable L y x := by
  unfold ResLayer.indistinguishable at h ⊢
  rw [commonDist_symm x y] at h
  exact h

-- 层 L 下的"同层"是等价关系（自反、对称、传递）——凝结（商）合法。
-- 直接由通用引理给出（旧的手写归纳已删）：不可区分对称 ⟹ 传递闭包成等价关系。
theorem ResLayer.related_equivalence (L : ResLayer) {n : ℕ} :
    Equivalence (ResLayer.related (n := n) L · ·) :=
  reflTransGen_equivalence (fun _ _ h => ResLayer.indistinguishable_symm L h)

-- 凝结 𝒦：在层 L 下，把"同层"（related）的状态凝成等价类（Setoid）。
def ResLayer.condense (L : ResLayer) {n : ℕ} : Setoid (StateQuant n) :=
  Setoid.mk (ResLayer.related L · ·) (ResLayer.related_equivalence L)

-- 层 L 下的凝结对象 = "同层等价类"的商（有限 sheaf 的截面空间）。
abbrev ResLayer.object (L : ResLayer) (n : ℕ) := Quotient (ResLayer.condense L (n := n))

-- 凝结唯一（sheaf 公理的有限版）：related（不可区分传递闭包）的状态凝成同一个对象。
-- 这就是范畴论 sheaf 的"局部相容 ⟹ 唯一粘合"，在有限分辨率层上的版本。
theorem ResLayer.condense_unique (L : ResLayer) {n : ℕ} {x y : StateQuant n}
    (h : ResLayer.related L x y) :
    (Quotient.mk (ResLayer.condense L) x : ResLayer.object L n) =
      Quotient.mk (ResLayer.condense L) y := by
  exact Quotient.sound h

-- related 单调（消解单调）：δ 增大（层变粗），同层关系扩张——越粗消解越多。
theorem ResLayer.related_mono {δ₁ δ₂ : ℚ} {n : ℕ} {x y : StateQuant n}
    (h : δ₁ ≤ δ₂) (hxy : ResLayer.related ⟨δ₁⟩ x y) : ResLayer.related ⟨δ₂⟩ x y :=
  reflTransGen_mono (fun _ _ hx => le_trans hx h) x y hxy

-- 消解 ℛ_D：细层对象 → 粗层对象（商映射，related_mono 保证良定义）。
-- 这是范畴论 sheaf 的"限制映射"在有限分辨率层上的反向版本。
def ResLayer.resolution {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) {n : ℕ} :
    ResLayer.object ⟨δ₁⟩ n → ResLayer.object ⟨δ₂⟩ n :=
  Quotient.map id (fun _ _ hxy => ResLayer.related_mono h hxy)

-- 凝结-消解 adjunction（消解是投影）：先凝结到细层再消解到粗层 = 直接凝结到粗层。
theorem ResLayer.resolution_condense {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) {n : ℕ} (x : StateQuant n) :
    ResLayer.resolution h (Quotient.mk (ResLayer.condense ⟨δ₁⟩) x) =
      (Quotient.mk (ResLayer.condense ⟨δ₂⟩) x : ResLayer.object ⟨δ₂⟩ n) := by
  unfold ResLayer.resolution
  rfl

-- 零阈值下不可区分 ⟺ val 相等（commonDist ≤ 0 ⟺ = 0 ⟺ val 相等）。
theorem ResLayer.indistinguishable_zero_iff {n : ℕ} (x y : StateQuant n) :
    ResLayer.indistinguishable ⟨0⟩ x y ↔ x.val = y.val := by
  unfold ResLayer.indistinguishable
  constructor
  · intro h
    have hnonneg : 0 ≤ commonDist x y := by
      rw [commonDist_same_dim]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have heq : commonDist x y = 0 := le_antisymm h hnonneg
    exact (commonDist_eq_zero_iff x y).mp heq
  · intro h
    exact le_of_eq ((commonDist_eq_zero_iff x y).mpr h)

-- 细层（δ=0）同层 ⟺ val 相等（零阈值下，related 退化为完全相等）。
theorem ResLayer.related_zero_iff {n : ℕ} (x y : StateQuant n) :
    ResLayer.related ⟨0⟩ x y ↔ x.val = y.val := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail hprev hlast ih =>
        exact ih.trans ((ResLayer.indistinguishable_zero_iff _ _).mp hlast)
  · intro h
    exact Relation.ReflTransGen.single ((ResLayer.indistinguishable_zero_iff x y).mpr h)

-- ============ 凝结范畴：resolution 是函子（预层 presheaf） ============

/-
  【预层（presheaf）：层 ↦ 凝结对象 是函子】

  范畴论：预层 = 从 site（site 的开集范畴）到 Type 的函子。
  这里：site = 层序 (ResLayer, ≤)（有限偏序范畴），
        预层 = L ↦ ResLayer.object L n（层 L 上的凝结对象空间），
        函子作用 = ResLayer.resolution（细层对象 → 粗层对象）。

  函子公理两条：恒等 + 复合（下面证）。
  这就是 Grothendieck 链的第一站：层（site）→ 预层 → （粘合后）sheaf → topos。
  关键是"有限"：site 是有限偏序（LayerLadder = Fin m），不是连续拓扑空间。
-/

-- 函子恒等：同层消解 = 恒等映射。
theorem ResLayer.resolution_id (δ : ℚ) {n : ℕ} :
    ResLayer.resolution (le_refl δ) (n := n) = id := by
  funext q
  induction q using Quotient.ind with
  | _ x => rfl

-- 函子复合：先消解 δ₁→δ₂ 再 δ₂→δ₃，等于直接消解 δ₁→δ₃。
-- 复合律成立 = 消解是"良定义的函子"（中间层不额外过滤，与 δThreshold_comp 同源）。
theorem ResLayer.resolution_comp {δ₁ δ₂ δ₃ : ℚ} (h₁ : δ₁ ≤ δ₂) (h₂ : δ₂ ≤ δ₃)
    {n : ℕ} (q : ResLayer.object ⟨δ₁⟩ n) :
    ResLayer.resolution h₂ (ResLayer.resolution h₁ q) =
      ResLayer.resolution (h₁.trans h₂) q := by
  induction q using Quotient.ind with
  | _ x => rfl

-- 预层定律：恒等 + 复合同时成立——(ResLayer, ≤) 上长出预层。
-- 这是有限 Grothendieck 链的第一站：site（有限层序）→ 预层（presheaf）。
theorem ResLayer.presheaf_laws {δ₁ δ₂ δ₃ : ℚ} (h₁ : δ₁ ≤ δ₂) (h₂ : δ₂ ≤ δ₃) {n : ℕ}
    (q : ResLayer.object ⟨δ₁⟩ n) :
    ResLayer.resolution (le_refl δ₁) q = q ∧
    ResLayer.resolution h₂ (ResLayer.resolution h₁ q) = ResLayer.resolution (h₁.trans h₂) q := by
  constructor
  · rw [ResLayer.resolution_id]
    rfl
  · exact ResLayer.resolution_comp h₁ h₂ q

-- 消解不可逆（差异论硬核）：细层可区分的对象，消解到粗层后合并（丢信息）。
-- 反例 δ₁=0（细）、δ₂=1（粗），val 0 与 val 1 在细层可分、在粗层不分——消解合并了它们。
theorem ResLayer.resolution_irreversible :
    ∃ δ₁ δ₂ : ℚ, δ₁ < δ₂ ∧ ∃ x y : StateQuant 1,
      ¬ ResLayer.related ⟨δ₁⟩ x y ∧ ResLayer.related ⟨δ₂⟩ x y := by
  refine ⟨0, 1, by norm_num, ?_⟩
  let x : StateQuant 1 := { val := fun _ => 0, phase := .neutral }
  let y : StateQuant 1 := { val := fun _ => 1, phase := .neutral }
  refine ⟨x, y, ?_⟩
  constructor
  · intro hxy
    have hval : x.val = y.val := (ResLayer.related_zero_iff x y).mp hxy
    have hne : x.val ≠ y.val := by
      intro h
      have h0 := congrFun h ⟨0, by norm_num⟩
      norm_num [x, y] at h0
    exact hne hval
  · exact Relation.ReflTransGen.single (by
      unfold ResLayer.indistinguishable
      rw [commonDist_same_dim]
      norm_num [x, y])

-- ============ 有限层序（差异阶梯）：有限 sheaf 的"有限" ============

/-
  【有限层序（D2 差异阶梯）：层序是有限离散台阶，不是连续 ℚ】

  D2：ℒ = {λ₀ > λ₁ > ... > λ_m}，有限台阶，严格递减。
  这钉死"拒连续统"：层序不是连续 ℚ 的任意子集，是有限离散台阶。
  ResLayer 的 δ 是单个 ℚ（连续），LayerLadder 把 δ 收进有限递减序列（Fin m）——
  有限 sheaf 的"有限"，就是这个 Fin m。
-/

-- 有限层序（差异阶梯）：m 个严格递减的分辨率台阶。
structure LayerLadder where
  m : ℕ
  δ : Fin m → ℚ
  h_dec : StrictAnti δ

-- 相邻台阶严格递减：δ (i+1) < δ i（下一层阈值更小，更细）。
theorem LayerLadder.adjacent_dec (L : LayerLadder) {i : Fin L.m} (h : i.val + 1 < L.m) :
    L.δ ⟨i.val + 1, h⟩ < L.δ i := by
  exact L.h_dec (Nat.lt_succ_self i.val)

-- 沿层序的逐层消解：从第 j 层（细）到第 i 层（粗，i < j）的 resolution。
-- 严格递减 ⟹ δ j < δ i，ResLayer.resolution（δ 小 → δ 大）良定义。
def LayerLadder.resolution (L : LayerLadder) {i j : Fin L.m} (h : i < j) {n : ℕ} :
    ResLayer.object ⟨L.δ j⟩ n → ResLayer.object ⟨L.δ i⟩ n :=
  ResLayer.resolution (le_of_lt (L.h_dec h))

-- 有限层序上的复合律：沿阶梯的逐层消解可复合（k → j → i = k → i）。
-- 这使有限层序成为一个"有限 site"，消解是它到 Type 的函子——预层的有限版。
theorem LayerLadder.resolution_comp (L : LayerLadder) {i j k : Fin L.m}
    (hij : i < j) (hjk : j < k) {n : ℕ} (q : ResLayer.object ⟨L.δ k⟩ n) :
    LayerLadder.resolution L hij (LayerLadder.resolution L hjk q) =
      LayerLadder.resolution L (lt_trans hij hjk) q := by
  unfold LayerLadder.resolution ResLayer.resolution
  induction q using Quotient.ind with
  | _ x => rfl

-- 层（site）上的预层 + 粘合 = 层（sheaf）：
-- 预层定律（函子恒等 + 复合）+ 粘合唯一（condense_unique）同时成立，
-- 这就是"有限 Grothendieck 层"（finite sheaf）的完整公理。
theorem ResLayer.sheaf_axioms {δ₁ δ₂ δ₃ : ℚ} (h₁ : δ₁ ≤ δ₂) (h₂ : δ₂ ≤ δ₃) {n : ℕ}
    (q : ResLayer.object ⟨δ₁⟩ n) {x y : StateQuant n} (hxy : ResLayer.related ⟨δ₁⟩ x y) :
    ResLayer.resolution (le_refl δ₁) q = q ∧
    ResLayer.resolution h₂ (ResLayer.resolution h₁ q) = ResLayer.resolution (h₁.trans h₂) q ∧
    (Quotient.mk (ResLayer.condense ⟨δ₁⟩) x : ResLayer.object ⟨δ₁⟩ n) =
      Quotient.mk (ResLayer.condense ⟨δ₁⟩) y := by
  have hpres := ResLayer.presheaf_laws h₁ h₂ q
  exact ⟨hpres.1, hpres.2, ResLayer.condense_unique ⟨δ₁⟩ hxy⟩

-- ============ sheaf 公理的真身：局部相容 ⟹ 全局粘合 ============

/-
  【sheaf 公理：局部相容 ⟹ 全局粘合（链式版）】

  范畴论 sheaf 公理：一族局部截面若在重叠处相容，则粘成唯一整体截面。
  有限版：一串状态 f 0, f 1, ..., f k，若每对相邻都不可区分（"局部相容"），
          则首尾 related（"可粘合"），且全部凝成同一个对象（"唯一整体"）。

  这是 sheaf 公理最朴素的形式——相容性是局部的（相邻），结论是全局的（全体同一）。
  中间的传递闭包 ReflTransGen 就是"粘合"本身。
-/

-- 局部相容 ⟹ 全局粘合：相邻逐对不可区分的一串状态，首尾 related。
-- 直接由通用粘合律 gluing_general 给出（旧的手写归纳已删）。
theorem ResLayer.gluing_sequence (L : ResLayer) {n : ℕ} {f : ℕ → StateQuant n} {k : ℕ}
    (h : ∀ i, i < k → ResLayer.indistinguishable L (f i) (f (i + 1))) :
    ResLayer.related L (f 0) (f k) :=
  gluing_general h

-- 局部相容 ⟹ 唯一整体：相邻不可区分的一串状态，全部凝成同一个对象。
-- 这正是 sheaf"局部相容数据粘贴成唯一整体"在有限分辨率层上的落地。
theorem ResLayer.gluing_condense (L : ResLayer) {n : ℕ} {f : ℕ → StateQuant n} {k : ℕ}
    (h : ∀ i, i < k → ResLayer.indistinguishable L (f i) (f (i + 1))) :
    (Quotient.mk (ResLayer.condense L) (f 0) : ResLayer.object L n) =
      Quotient.mk (ResLayer.condense L) (f k) :=
  ResLayer.condense_unique L (ResLayer.gluing_sequence L h)

-- ============ 消解损失 = 粘合障碍（有限 H⁰）与差异论的分歧 ============

/-
  【消解损失：Grothendieck 的"粘合缺陷" vs 差异论的"时间之箭"】

  Grothendieck：限制映射 F(U) → F(V) 是 sheaf 数据的一部分；局部截面唯一决定
  整体截面（粘合），而整体限制到局部也完全可逆（局部数据 = 整体的切片）。
  上同调 H^i 度量的是"粘合失败的程度"——它是**缺陷**，理想情形是 H^i = 0。

  差异论：凝结（粘合）成立（gluing_condense），但**消解没有逆**——
  粗层永远恢复不出细层。而且这不是缺陷，是**必然**：
  有限性（n < 2^n）保证洞存在，消解必然把不同的细层对象合并。
  所以差异论的"粘合障碍"不是可以消掉的缺陷，是**熵——时间之箭**。

  三条定理钉死这个分歧：
    (a) resolution_surjective         —— 消解是满射（粘合方向通）；
    (b) resolution_injective_iff      —— 消解单射 ⟺ 不合并任何东西（损失为零）；
    (c) resolution_not_injective      —— 存在严格更粗的层，消解必然不单射（损失必然）。
  (a)+(c) 合起来：**粘合可行，反粘合必然失败**——这就是"半 sheaf"。
-/

-- (a) 消解是满射：任何粗层对象都来自某个细层对象（粘合方向总是通的）。
theorem ResLayer.resolution_surjective {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) {n : ℕ} :
    Function.Surjective (ResLayer.resolution (n := n) h) := by
  intro q
  induction q using Quotient.ind with
  | _ x => exact ⟨Quotient.mk (ResLayer.condense ⟨δ₁⟩) x, rfl⟩

-- (b) 消解损失为零（单射）⟺ 粗层没有合并任何新的东西。
-- 这是有限 H⁰ 的精确刻画：restriction 是单射 ⟺ 无障碍。
theorem ResLayer.resolution_injective_iff {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) {n : ℕ} :
    Function.Injective (ResLayer.resolution (n := n) h) ↔
      ∀ x y : StateQuant n, ResLayer.related ⟨δ₂⟩ x y → ResLayer.related ⟨δ₁⟩ x y := by
  constructor
  · intro hinj x y hxy
    have hq : (Quotient.mk (ResLayer.condense ⟨δ₁⟩) x : ResLayer.object ⟨δ₁⟩ n) =
        Quotient.mk (ResLayer.condense ⟨δ₁⟩) y := by
      apply hinj
      rw [ResLayer.resolution_condense, ResLayer.resolution_condense]
      exact ResLayer.condense_unique ⟨δ₂⟩ hxy
    exact Quotient.exact hq
  · intro hno q₁ q₂ hq
    induction q₁ using Quotient.ind with
    | _ x =>
      induction q₂ using Quotient.ind with
      | _ y =>
        have hrel₂ : ResLayer.related ⟨δ₂⟩ x y := by
          have heq : (Quotient.mk (ResLayer.condense ⟨δ₂⟩) x : ResLayer.object ⟨δ₂⟩ n) =
              Quotient.mk (ResLayer.condense ⟨δ₂⟩) y := hq
          exact Quotient.exact heq
        exact Quotient.sound (hno x y hrel₂)

-- (c) 损失必然：存在严格更粗的层，消解不单射（必然合并）。
-- 与 (a) 合起来 = "半 sheaf"：粘合可行，反粘合必然失败。
theorem ResLayer.resolution_not_injective :
    ∃ (δ₁ δ₂ : ℚ) (_hlt : δ₁ < δ₂), ∃ x y : StateQuant 1,
      ResLayer.related ⟨δ₂⟩ x y ∧ ¬ ResLayer.related ⟨δ₁⟩ x y := by
  obtain ⟨δ₁, δ₂, hlt, x, y, hx, hy⟩ := ResLayer.resolution_irreversible
  exact ⟨δ₁, δ₂, hlt, x, y, hy, hx⟩

-- ============ 桥：层 → 差异环（层与几何无关） ============

/-
  【桥：差异环和分辨率层是同一个"层"构造】

  差异论有两个"几何"：
    · 色环 C_k：Fin k，不可区分 = hueDist ≤ δ（环距离）
    · 状态空间：StateQuant n，不可区分 = commonDist ≤ δ（欧氏距离平方）

  这里证明：**两者的层结构完全同构**——都走同一条链：
    对称的不可区分关系 r
      → 传递闭包 ReflTransGen r（因 r 不传递：色距/欧氏距离都不满足三角不等式）
      → 等价关系（因 r 对称）
      → 商（凝结对象）
      → 层定律：粘合满射 + 零损失 ⟺ 无新合并

  "层"不依赖几何（环距离还是欧氏距离），只依赖"对称关系"。
  所以差异环只是层在圆几何上的一个实例——这就是"层 → 差异环"的桥。
-/

-- 桥的落地（色环侧）：色环的"同类"就是色距的不可区分关系。
theorem sameHueClass_iff_hueIndist {k : ℕ} (a b : Fin k) (δ : ℕ) :
    sameHueClass a b δ ↔ hueDist a b ≤ δ := Iff.rfl

-- 桥的落地（色环侧）：色环的"同类"（传递闭包）= 色距关系的传递闭包，
-- 和 ResLayer.related 完全同构——差异环就是层在圆几何上的实例。
theorem sameHueClassTrans_iff_closure {k : ℕ} (a b : Fin k) (δ : ℕ) :
    sameHueClassTrans a b δ ↔
      Relation.ReflTransGen (fun x y : Fin k => hueDist x y ≤ δ) a b := Iff.rfl

-- 桥的结论：两种几何的层定律，是 layer_law 的两个实例。
-- 色环（hueDist）与状态空间（commonDist）在"层"的意义下没有区别。
theorem layer_law_instances :
    (∀ (k : ℕ) (δ₁ δ₂ : ℕ), δ₁ ≤ δ₂ →
      classCount (k := k) δ₂ ≤ classCount (k := k) δ₁) ∧
    (∀ (δ₁ δ₂ : ℚ) (h : δ₁ ≤ δ₂),
      Function.Surjective (ResLayer.resolution (n := 1) h)) :=
  ⟨fun _ _ _ h => classCount_antitone h,
   fun _ _ h => ResLayer.resolution_surjective h⟩

-- ============ 覆盖定理：理论的两个几何都是层几何的实例 ============

/-- 色环是层几何：不可区分 = 色距 ≤ δ（δ 用 ℚ 表述，便于与层几何统一）。 -/
def ringGeometry (k : ℕ) : LayerGeometry (Fin k) where
  indist δ a b := (hueDist a b : ℚ) ≤ δ
  h_symm := fun _ a b h => by
    rw [hueDist_symm a b] at h
    exact h
  h_mono := fun _ _ h _ _ hab => le_trans hab h

/-- 状态空间是层几何：不可区分 = 共同距离 ≤ δ。 -/
def stateGeometry (n : ℕ) : LayerGeometry (StateQuant n) where
  indist δ x y := commonDist x y ≤ δ
  h_symm := fun _ x y h => by
    rw [commonDist_symm x y] at h
    exact h
  h_mono := fun _ _ h _ _ hab => le_trans hab h

-- 桥（色环）：理论的"同类"就是层几何的 related（ℕ 阈值 ↔ ℚ 阈值）。
theorem ring_instance_bridge {k : ℕ} (a b : Fin k) (δ : ℕ) :
    sameHueClassTrans a b δ ↔ LayerGeometry.related (ringGeometry k) (δ : ℚ) a b := by
  change Relation.ReflTransGen (fun x y : Fin k => hueDist x y ≤ δ) a b ↔
    Relation.ReflTransGen (fun x y : Fin k => (hueDist x y : ℚ) ≤ (δ : ℚ)) a b
  exact reflTransGen_congr (fun x y => by
    constructor <;> intro h <;> exact_mod_cast h) a b

-- 桥（状态空间）：理论的"同类"就是层几何的 related（定义一致）。
theorem state_instance_bridge {n : ℕ} (δ : ℚ) (x y : StateQuant n) :
    ResLayer.related ⟨δ⟩ x y ↔ LayerGeometry.related (stateGeometry n) δ x y := Iff.rfl

/-
  【覆盖定理】

  差异论的两个几何（色环、状态空间）都是 LayerGeometry 的实例，且：
    (1)(2) 理论自己的"同类"与层几何的 related 定义一致（桥）；
    (3)(4) 层定律（凝结满射）对两个几何自动成立。

  于是"层"的全部定理——等价关系、单调、凝结、粘合、损失刻画——
  不需为每个几何重证，都是 LayerGeometry 上的通用事实的代入。
-/
theorem theory_layer_coverage :
    (∀ (k : ℕ) (a b : Fin k) (δ : ℕ),
        sameHueClassTrans a b δ ↔ LayerGeometry.related (ringGeometry k) (δ : ℚ) a b) ∧
    (∀ (n : ℕ) (δ : ℚ) (x y : StateQuant n),
        ResLayer.related ⟨δ⟩ x y ↔ LayerGeometry.related (stateGeometry n) δ x y) ∧
    (∀ (k : ℕ) (δ₁ δ₂ : ℚ) (h : δ₁ ≤ δ₂),
        Function.Surjective ((ringGeometry k).condense h)) ∧
    (∀ (n : ℕ) (δ₁ δ₂ : ℚ) (h : δ₁ ≤ δ₂),
        Function.Surjective ((stateGeometry n).condense h)) :=
  ⟨fun _ a b δ => ring_instance_bridge a b δ,
   fun _ δ x y => state_instance_bridge δ x y,
   fun k _ _ h => (ringGeometry k).condense_surjective h,
   fun n _ _ h => (stateGeometry n).condense_surjective h⟩

-- 态射到分辨族：f 的"画像"是 B 个分辨（每个 b 判"a 是否映射到 b"）。
def morphismToResolves {A B : Type*} [DecidableEq B] (f : A → B) : B → resolveSpace A :=
  fun b a => decide (f a = b)

-- 函数性：每个 a 恰好一个 b 使得 p b a = true（定向：每个 a 指向唯一 b）。
def IsFunctional {A B : Type*} (p : B → resolveSpace A) : Prop :=
  ∀ a : A, ∃! b : B, p b a = true

-- 态射的分辨族是函数性的（每个 a 恰好映射到一个 b）。
theorem morphismToResolves_functional {A B : Type*} [DecidableEq B] (f : A → B) :
    IsFunctional (morphismToResolves f) := by
  intro a
  refine ⟨f a, ?_, ?_⟩
  · simp [morphismToResolves]
  · intro b hb
    have hf : f a = b := by simpa [morphismToResolves] using hb
    exact hf.symm

-- 态射由分辨族单射决定（态射 = 分辨族的画像，构造性、无 Classical）。
theorem morphism_resolves_injective {A B : Type*} [DecidableEq B] :
    Function.Injective (morphismToResolves (A := A) (B := B)) := by
  intro f g h
  funext a
  have hfg := congrFun (congrFun h (f a)) a
  have hg : g a = f a := by
    simpa [morphismToResolves] using hfg.symm
  exact hg.symm

-- 从函数性分辨族重构态射：f a = 唯一的 b。
-- 构造性（无 Classical）：用 Fintype + LinearOrder 的 min' 选最小 b。
-- 有限性替代 Classical 来做"选择"——这正是 finite_choice_free 的精神。
def functionalToMorphism {A B : Type*} [Fintype B] [LinearOrder B] [DecidableEq B]
    (p : B → resolveSpace A) (h : IsFunctional p) : A → B :=
  fun a => (Finset.univ.filter (fun b => p b a = true)).min' (by
    rcases h a with ⟨b, hb, _⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩⟩
  )

-- 态射 ≃ 分辨（右逆）：从态射绕一圈（态射 → 分辨族 → 态射）回来还是原态射。
-- functionalToMorphism ∘ morphismToResolves = id，态射被分辨族完全记住。
theorem functionalToMorphism_morphismToResolves {A B : Type*} [Fintype B] [LinearOrder B] [DecidableEq B]
    (f : A → B) :
    functionalToMorphism (morphismToResolves f) (morphismToResolves_functional f) = f := by
  funext a
  unfold functionalToMorphism morphismToResolves
  rw [Finset.min'_eq_iff]
  constructor
  · simp
  · intro b hb
    exact le_of_eq (by simpa using (Finset.mem_filter.mp hb).2)

-- 态射 ≃ 分辨（左逆）：从分辨族绕一圈（分辨族 → 态射 → 分辨族）回来还是原分辨族。
-- morphismToResolves ∘ functionalToMorphism = id（在函数性分辨族上）。
-- 两者互为逆 = 态射与"函数性分辨族"是同一个对象（闭环）。
theorem morphismToResolves_functionalToMorphism {A B : Type*} [Fintype B] [LinearOrder B] [DecidableEq B]
    (p : B → resolveSpace A) (h : IsFunctional p) :
    morphismToResolves (functionalToMorphism p h) = p := by
  funext b a
  unfold morphismToResolves
  obtain ⟨b0, hb0, huniq⟩ := h a
  have hftm : functionalToMorphism p h a = b0 := by
    unfold functionalToMorphism
    rw [Finset.min'_eq_iff]
    constructor
    · simp [hb0]
    · intro b' hb'
      exact le_of_eq (huniq b' (Finset.mem_filter.mp hb').2).symm
  rw [hftm]
  by_cases hbb0 : b0 = b
  · rw [← hbb0]
    simp [hb0]
  · have hbf : p b a = false := by
      cases hpb : p b a with
      | true =>
          have hbb : b = b0 := huniq b hpb
          exact False.elim (hbb0 hbb.symm)
      | false => rfl
    rw [hbf]
    simp [hbb0]

-- ============ 对位：洞与有的互补 ============

/-
  【对位 = 互补填洞】

  "你选择用这个洞（对上），来作为自己的洞"——"对上"就是"对位"。

  x 的洞（补 0 的缝隙 [m, max m n)）= 无。
  y 的有（这些维度上的量）= 有。
  对位 = y 的有恰好填进 x 的洞（互补）。

  层间转移的三分（对位的一条完整路径）：
    t = 0   → 纯洞（死界，valOrZero x i = 0）
    t = 1/2 → 暹界临界（半值，halfValue_equidistant 等距）
    t = 1   → 洞被填满（生界，对位完成）

  这是《暹界定理》"交易的本质在暹界"的几何化：
  交易成立 = 互补洞在暹界处完成层间转移对位。
-/

-- 互补：y 的有（非 0）恰好填在 [m, max m n) 的洞（补 0 的缝隙）上。
def Complementary {m n : ℕ} (y : StateQuant n) : Prop :=
  ∀ i : Fin (max m n), m ≤ i.val → valOrZero y i ≠ 0

-- 对位完成：t = 1 时，x 的洞被 y 的实完全填满。
theorem alignment_complete {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (i : Fin (max m n)) (hi : m ≤ i.val) :
    crossDimPath x y 1 i = valOrZero y i := by
  simpa using hole_connection x y 1 i hi

-- 互补 ⇒ 对位处处有量（交易成立）：互补洞上，路径处处非零。
theorem complementary_alignment {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (h : Complementary (m := m) y) (t : ℚ) (ht : t ≠ 0) (i : Fin (max m n)) (hi : m ≤ i.val) :
    crossDimPath x y t i ≠ 0 := by
  exact hole_connection_nonzero x y t ht i hi (h i hi)

-- 对位守恒（D7 的几何版）：洞（0）被有填满，量守恒——x 的洞不贡献，y 的有全保留。
theorem alignment_conservation {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (i : Fin (max m n)) (hi : m ≤ i.val) :
    valOrZero x i + crossDimPath x y 1 i = valOrZero y i := by
  have hzero : valOrZero x i = 0 := valOrZero_hole x i hi
  have hfill : crossDimPath x y 1 i = valOrZero y i := alignment_complete x y i hi
  rw [hzero, hfill]
  ring

-- ============ 分辨（情绪）vs 对位（理性） ============

/-
  【情绪 = 分辨，理性 = 对位；分辨不保证理性的充分】

  分辨（resolveSpace α = α → Bool）是"一分为二"：每维一个布尔判定，
  只判"有/无"，判不出"填在哪"——这是情绪，粗糙的二分（喜/恶、安/危）。

  对位（Complementary）是"互补填洞"：y 的非零恰好落在 x 的洞 [m, n) 上。
  这是理性，精确的对齐（洞被有填满）。

  两个方向不对称：
    (1) 对位 ⟹ 分辨（complementary_resolve）：填洞必有量，有量即可二分。
    (2) 分辨 ⟹̸ 对位（resolve_not_complementary）：有量未必填在洞上。
  故"对位才是理性，分辨不保证理性的充分"——情绪是理性的必要不充分条件。
-/

-- (1) 对位 ⟹ 分辨：互补填洞必有非零分量（差异），有差异才能二分。
theorem complementary_resolve {m n : ℕ} (y : StateQuant n) (h : Complementary (m := m) y)
    (hmn : m < n) : ∃ i : Fin n, y.val i ≠ 0 := by
  let i : Fin n := ⟨m, hmn⟩
  refine ⟨i, ?_⟩
  have hmax : max m n = n := max_eq_right (Nat.le_of_lt hmn)
  let j : Fin (max m n) := ⟨m, by rw [hmax]; exact hmn⟩
  have hj : m ≤ j.val := by simp [j]
  have hne : valOrZero y j ≠ 0 := h j hj
  have hval : valOrZero y j = y.val i := by
    unfold valOrZero
    simp [j, i, hmn]
  simpa [hval] using hne

-- (2) 分辨 ⟹̸ 对位：有量（可二分）未必填在洞上——情绪不保证理性。
--     反例 n = 2, y = (1, 0)：第 0 维有量（可分辨），洞 [1, 2) 是零（没填）。
theorem resolve_not_complementary :
    ∃ n : ℕ, ∃ y : StateQuant n,
      (∃ i : Fin n, y.val i ≠ 0) ∧ ¬ Complementary (m := 1) y := by
  let y : StateQuant 2 := { val := fun i => if i.val = 0 then 1 else 0, phase := .neutral }
  refine ⟨2, y, ?_, ?_⟩
  · -- 有分辨：第 0 维非零
    refine ⟨⟨0, by norm_num⟩, ?_⟩
    simp [y]
  · -- 无对位：洞 ⟨1⟩ 处是零（Complementary 要求 [1, 2) 维非零）
    intro hc
    have hne : valOrZero y (⟨1, by norm_num⟩ : Fin (max 1 2)) ≠ 0 := hc ⟨1, by norm_num⟩ (by norm_num)
    have hzero : valOrZero y (⟨1, by norm_num⟩ : Fin (max 1 2)) = 0 := by
      unfold valOrZero
      simp [y]
    exact hne hzero

-- ============ 架桥：差异值 → 分辨的秩（势） ============

/-
  【桥：状态差异值投影到分辨的秩】

  那位"资深 AI"指出的 gap：布尔格 + 秩是"分辨"层面，δ 是"差异值"层面。

  桥：差向量（valOrZero x - valOrZero y）通过阈值 δ 阈值化，
  得到"支持集"（差异超过 δ 的维度）——这是 Finset = 分辨。
  它的势（card）= 分辨的秩。

  于是差异值的"阈值 δ"投影成"势"（差异广度）：
    - 势有界（≤ max m n）——有限层；
    - 势随 δ 单调递减——分层（阈值递增，差异广度递减）。

  这就把"差异值的分层"和"分辨的势分层"对齐了：
  δ 不是外给的，它被"势"（有限、离散）钉住——δ 的有效取值是有限的。
-/

-- 差异广度：差异超过阈值 δ 的维度数（势 = 分辨的秩）。
def diffSupport {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (max m n) => δ < |valOrZero x i - valOrZero y i|)).card

-- 势有界：差异广度 ≤ 总维度（有限层，不会无限分层）。
theorem diffSupport_le {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    diffSupport x y δ ≤ max m n := by
  unfold diffSupport
  simpa using (Finset.card_filter_le Finset.univ
    (fun i : Fin (max m n) => δ < |valOrZero x i - valOrZero y i|))

-- 势随阈值单调递减：δ 越大，差异广度越小（阈值递增 = 层递减，形成分层）。
theorem diffSupport_antitone {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    diffSupport x y δ₂ ≤ diffSupport x y δ₁ := by
  unfold diffSupport
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_le_of_lt h hi.2⟩

-- ============ δ 方向的分辨率转移：死界 → 生界 ============

/-
  【δ 方向的分辨率转移（深水区 1 的第一铲）】

  coarsen/condense 是"维度转移"（投影 / 补 0）。这里做"δ 方向"的转移：
  δ 减小 = 分辨率升高，原来在死界（|diff| ≤ δ₂）的维度，跨过阈值后进入
  生界（δ₁ < |diff|）——分辨的势（diffSupport）严格增大。

  这是"死界 → 生界"的精确形式：δ 从 δ₂ 降到 δ₁，若跨过某个维度的差异值
  （δ₁ < |diff i| ≤ δ₂），则该维度从死界翻到生界，势严格增。
  呼应"分辨 = 低分辨率、对位 = 高分辨率"——δ 减小就是从分辨爬到对位。
-/

-- 严格转移：δ 减小跨过差异值时，分辨势严格增大（死界 → 生界）。
theorem diffSupport_strict_antitone {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ₁ δ₂ : ℚ} (hδ : δ₁ < δ₂)
    (hi : ∃ i : Fin (max m n), δ₁ < |valOrZero x i - valOrZero y i| ∧ |valOrZero x i - valOrZero y i| ≤ δ₂) :
    diffSupport x y δ₂ < diffSupport x y δ₁ := by
  unfold diffSupport
  obtain ⟨i, hi_lt, hi_le⟩ := hi
  let s₁ : Finset (Fin (max m n)) := Finset.univ.filter (fun j => δ₁ < |valOrZero x j - valOrZero y j|)
  let s₂ : Finset (Fin (max m n)) := Finset.univ.filter (fun j => δ₂ < |valOrZero x j - valOrZero y j|)
  change s₂.card < s₁.card
  apply Finset.card_lt_card
  constructor
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, lt_trans hδ hj.2⟩
  · intro h
    have hi_in_s1 : i ∈ s₁ := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hi_lt⟩
    have hi_not_in_s2 : i ∉ s₂ := by
      intro h2
      rw [Finset.mem_filter] at h2
      exact not_lt_of_ge hi_le h2.2
    exact hi_not_in_s2 (h hi_in_s1)

-- ============ 任务 A：δ 方向的凝结/消解算子（阈值化） ============

/-
  【δ 方向的分辨率转移：阈值化算子本体】

  coarsen/condense 是"维度转移"（投影 / 补 0）。这里是"δ 方向"的算子：
  δThreshold δ z 把差异值 z 在阈值 δ 下阈值化——死界（|z| ≤ δ）凝结归 0
  （不可区分，看起来相同），生界（|z| > δ）保留（可区分）。

  这对应 D6 消解：分辨率降低（δ 大）时，低差异被消解成"看起来相同"（归 0）。
  δ 减小（精化/凝结）则相反：被归 0 的差异重新翻到生界（恢复可区分）。

  幂等（再阈值化不变）、不增大差异（|δThreshold z| ≤ |z|）是它的两条基本性质。
-/

-- δ 阈值化：死界（|z| ≤ δ）凝结归 0，生界（|z| > δ）保留。
def δThreshold (δ z : ℚ) : ℚ := if |z| ≤ δ then 0 else z

-- 死界凝结：|z| ≤ δ 时归 0（消解成"看起来相同"）。
theorem δThreshold_dead {δ z : ℚ} (h : |z| ≤ δ) : δThreshold δ z = 0 := by
  unfold δThreshold
  simp [h]

-- 生界保留：δ < |z| 时保留（可区分）。
theorem δThreshold_living {δ z : ℚ} (h : δ < |z|) : δThreshold δ z = z := by
  unfold δThreshold
  simp [not_le_of_gt h]

-- 幂等：再阈值化不变（死界已归 0，生界保留）。
theorem δThreshold_idempotent (δ z : ℚ) : δThreshold δ (δThreshold δ z) = δThreshold δ z := by
  unfold δThreshold
  by_cases h : |z| ≤ δ <;> simp [h]

-- 消解不增大差异：|δThreshold z| ≤ |z|（阈值化是压低，不放大）。
theorem δThreshold_abs_le (δ z : ℚ) : |δThreshold δ z| ≤ |z| := by
  unfold δThreshold
  by_cases h : |z| ≤ δ
  · simp [h]
  · simp [h]

-- δ 消解单调（δ 方向凝结/消解，深水区 #1）：δ 增大，阈值化消解更多（死界单调扩张）。
-- δ 减小=凝结（生界浮出），δ 增大=消解（死界扩张），单调不可逆——
-- 与维度版 coarsen/condense（互为逆）不同，δ 版是单向的"分辨率转移"。
theorem δThreshold_monotone {δ₁ δ₂ z : ℚ} (h : δ₁ ≤ δ₂) :
    |δThreshold δ₂ z| ≤ |δThreshold δ₁ z| := by
  unfold δThreshold
  by_cases h₁ : |z| ≤ δ₁
  · have h₂ : |z| ≤ δ₂ := le_trans h₁ h
    simp [h₁, h₂]
  · by_cases h₂ : |z| ≤ δ₂
    · simp [h₁, h₂]
    · simp [h₁, h₂]

-- 跨层投影 = 逐层消解（投影算子 π 的 δ 版）：δ₁ ≤ δ₂ 时，先阈值化到 δ₁ 再阈值化到 δ₂，
-- 等于直接阈值化到 δ₂。逐层消解（ℛ_D 迭代）的合成 = 跨层凝结（π）。
-- δ 阈值化单调，中间层不额外过滤——δ 从有限集合逼出，中间层不引入新台阶。
theorem δThreshold_comp {δ₁ δ₂ z : ℚ} (h : δ₁ ≤ δ₂) :
    δThreshold δ₂ (δThreshold δ₁ z) = δThreshold δ₂ z := by
  unfold δThreshold
  by_cases h₁ : |z| ≤ δ₁
  · have h₂ : |z| ≤ δ₂ := le_trans h₁ h
    simp [h₁, h₂]
  · by_cases h₂ : |z| ≤ δ₂
    · simp [h₁, h₂]
    · simp [h₁, h₂]

-- 逐层 = 跨层 恰好需要单调性：非单调（δ₂ < δ₁）时，先粗后细 ≠ 直接细。
-- 中间层（δ₁）额外过滤掉了 δ₂ 不会过滤的差异——这就是原文"r 非平凡 / 中间层额外过滤"的根源。
theorem δThreshold_comp_needs_monotone :
    ∃ δ₁ δ₂ z : ℚ, δThreshold δ₂ (δThreshold δ₁ z) ≠ δThreshold δ₂ z := by
  refine ⟨1, 0, (1 / 2 : ℚ), ?_⟩
  norm_num [δThreshold]

-- 阈值化保持分辨势：凝结掉的是死界（|z| ≤ δ，本就不在 diffSupport 里），
-- 生界（|z| > δ）保留，所以 |diff| > δ 的维度数不变。
theorem δThreshold_preserves_support {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    (Finset.univ.filter (fun i : Fin (max m n) => δ < |δThreshold δ (valOrZero x i - valOrZero y i)|)).card
      = diffSupport x y δ := by
  unfold diffSupport
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, lt_of_lt_of_le h.2 (δThreshold_abs_le δ (valOrZero x i - valOrZero y i))⟩
  · intro h
    rw [δThreshold_living h.2]
    exact h

-- δ 精化增益：从 δ₂ 精化到 δ₁（δ₁ ≤ δ₂），死界翻到生界的维度数（分辨势增量）。
def refineGain {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ₁ δ₂ : ℚ) : ℕ :=
  diffSupport x y δ₁ - diffSupport x y δ₂

-- 强度 ↔ 广度：差异强度（crossDimNormSq）≥ 阈值² × 差异广度（势）。
-- 每个超过 δ 的维度至少贡献 δ² 到平方和，于是"强度"和"广度"咬上了。
theorem crossDimNormSq_ge_support {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (δ : ℚ) (hδ : 0 ≤ δ) :
    δ^2 * (diffSupport x y δ : ℚ) ≤ crossDimNormSq x y := by
  unfold crossDimNormSq diffSupport
  let s : Finset (Fin (max m n)) := Finset.univ.filter (fun i => δ < |valOrZero x i - valOrZero y i|)
  calc
    δ^2 * (s.card : ℚ) = ∑ i ∈ s, (δ^2 : ℚ) := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ s, (valOrZero x i - valOrZero y i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hz : δ < |valOrZero x i - valOrZero y i| := (Finset.mem_filter.mp hi).2
      calc
        δ^2 ≤ |valOrZero x i - valOrZero y i|^2 :=
          sq_le_sq.mpr (by simpa [abs_of_nonneg hδ] using le_of_lt hz)
        _ = (valOrZero x i - valOrZero y i)^2 := by rw [sq_abs]
    _ ≤ ∑ i ∈ Finset.univ, (valOrZero x i - valOrZero y i)^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i _
        exact Finset.mem_univ i
      · intro i _ _
        exact sq_nonneg (valOrZero x i - valOrZero y i)

-- ============ δ 显式构造：阈值集合（势的台阶） ============

/-
  【δ 从势显式推出】

  δ 的"有效取值"（改变势的 δ）= 差异的绝对值 |z_i|（z_i = valOrZero x i − valOrZero y i）。

  这些绝对值构成一个有限集合 absDiffVals（≤ max m n 个），
  势 diffSupport 是 δ 的阶梯函数，台阶恰在这些绝对值处。

  所以 δ 从"有限性"显式推出：
    - 阈值集合有限（≤ max m n）；
    - 势只被阈值集合决定（δ 落在同一区间 → 势相同）。
-/

-- 阈值集合：差异的绝对值 |z_i|（有限，去重）。
def absDiffVals {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : Finset ℚ :=
  (Finset.univ : Finset (Fin (max m n))).image
    (fun i : Fin (max m n) => |valOrZero x i - valOrZero y i|)

-- 阈值集合有限：≤ max m n 个（δ 的有效取值有限，从有限性推出）。
theorem absDiffVals_card_le {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    (absDiffVals x y).card ≤ max m n := by
  unfold absDiffVals
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin (max m n))))
    (f := fun i : Fin (max m n) => |valOrZero x i - valOrZero y i|)
  simpa [Fintype.card_fin] using h

-- 势只被阈值集合决定：δ₁、δ₂ 对每个绝对值有相同的"<"关系 → 势相同。
theorem diffSupport_eq_of_no_abs_between {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ₁ δ₂ : ℚ} (h : ∀ a ∈ absDiffVals x y, δ₁ < a ↔ δ₂ < a) :
    diffSupport x y δ₁ = diffSupport x y δ₂ := by
  unfold diffSupport
  congr 1
  ext i
  have hmem : |valOrZero x i - valOrZero y i| ∈ absDiffVals x y := by
    unfold absDiffVals
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hiff := h (|valOrZero x i - valOrZero y i|) hmem
  rw [Finset.mem_filter, Finset.mem_filter]
  simpa using hiff

-- ============ 归约：根概念钉到三个真根 ============

/-
  【归约：验证"根概念"是有限性 / 差异 / ℚ 的特例】

  真根只有三个：差异（差 x_i − y_i）、ℚ（代数 + 线性序）、有限性（Fin）。

  这里验证：之前的"根概念"是这三个根的特例，不是独立原语。
  s_rel（无阈值差异计数）是 diffSupport（有阈值差异广度）在 δ = 0 的特例，
  而 diffSupport 从有限性（Finset 计数）来——所以 s_rel 是有限性特例。
-/

-- s_rel = diffSupport 0（同维）：无阈值差异计数 = 有阈值差异广度在 δ = 0 的特例。
-- 这验证 s_rel 是"有限性特例"——它被 diffSupport（从有限性来的势）覆盖。
theorem s_rel_eq_diffSupport_zero {n : ℕ} (x y : StateQuant n) :
    s_rel x y = diffSupport x y 0 := by
  rw [s_rel_same_dim]
  unfold diffSupport
  rw [Nat.max_self]
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [valOrZero_self_dim, abs_pos, sub_ne_zero]

-- ============ 焊：Ego ↔ Fluid（守恒与对位的统一） ============

/-
  【焊：把 Ego 底层接到 Fluid 应用层（"水怎么上来的"）】

  Ego 层（底层）：差异、分辨、洞、澄明、对位、守恒（D7）、δ 归约。
  Fluid 层（应用）：微团、质量、碰撞、合并、生存博弈。

  概念对应：
    Fluid.mass       ↔ Ego 总量（∑ x_i，线性守恒）
    Fluid.fluidDist  ↔ Ego commonDist（差异平方和）
    Fluid.collide    ↔ Ego layer（三分）+ D（phase 判定）
    Fluid.merge      ↔ Ego 对位（洞被有填满）
    Fluid.threshold  ↔ Ego δ（层化阈值，从有限性推出）

  核心焊：守恒的统一。Fluid 的 merge_mass_conservation（质量相加守恒）、
  Ego 的 D7（差异守恒）、alignment_conservation（对位守恒），
  都是同一个"加法守恒"（总量在层间转移中不变）的三种读数。

  "水怎么上来的"的答案在这里：差异守恒（D7）在流体层显影为质量守恒（merge）。
  高处的水养低处的水（以实养虚），靠的不是"推力"，是守恒——总量不灭，
  所以高处的"有"（质量）能填低处的"洞"（相对不足），这就是对位、这就是交易。
-/

-- 合并守恒（D7 的线性版 = Fluid 的 merge_mass_conservation 的 Ego 版）：
-- 合并（分量相加）保持总量不变——总量守恒是"水怎么上来的"的根。
theorem sum_merge_conservation {n : ℕ} (x y : StateQuant n) :
    (∑ i : Fin n, (x.val i + y.val i)) = (∑ i : Fin n, x.val i) + (∑ i : Fin n, y.val i) := by
  rw [Finset.sum_add_distrib]

-- 对位守恒的合并版：洞（0）与有（量）相加，总量不变——合并就是"对位"（洞被有填满）。
theorem alignment_merge_conservation {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (i : Fin (max m n)) (hi : m ≤ i.val) :
    valOrZero x i + valOrZero y i = valOrZero y i := by
  rw [valOrZero_hole x i hi]
  ring

-- ============ 真焊：merge 守恒 = D7 守恒（加法守恒的统一） ============

/-
  【真焊：把 Fluid 的 merge_mass_conservation 重证成 D7 特例】

  Fluid 层：merge（质量相加，质心加权）保持 mass 守恒。
  Ego 层：D7（差异守恒）说"凝结不消灭差异，只转移"。

  共同根是"加法守恒"：总量在"加"下不变。
  · D7（分解）：账本 s 按 P 分两份，两份之和 = 总量。
  · merge（合成）：两个分量合成一个，总量 = 分量之和。

  下面定义 stateMerge（Fluid merge 的 Ego 版，逐维相加），证它的守恒
  就是"加法守恒"，与 D7 同源——"水怎么上来的"（质量守恒 = 差异守恒）。
-/

-- 合并（Fluid merge 的 Ego 版）：两个状态逐维相加，总量 = 分量之和。
def stateMerge {n : ℕ} (x y : StateQuant n) : StateQuant n :=
  { val := fun i => x.val i + y.val i, phase := x.phase }

-- 真焊（守恒）：合并保持总量守恒（∑ 合成 = ∑ 分量之和）。
theorem stateMerge_conservation {n : ℕ} (x y : StateQuant n) :
    (∑ i : Fin n, (stateMerge x y).val i) = (∑ i : Fin n, x.val i) + (∑ i : Fin n, y.val i) := by
  unfold stateMerge
  rw [Finset.sum_add_distrib]

-- 真焊（D7 同源）：合并的第 i 维 = 二元账本 {x_i, y_i} 的总量（D7 的"总量"）。
-- 合成（merge）= 分解（D7 账本 sum），都是"加法守恒"。
theorem stateMerge_dim_is_D7 {n : ℕ} (x y : StateQuant n) (i : Fin n) :
    (stateMerge x y).val i =
      (Finset.univ : Finset (Fin 2)).sum (fun j => if j = 0 then x.val i else y.val i) := by
  unfold stateMerge
  simp [Fin.sum_univ_two]

-- ============ 交易：互补填洞（不是零和，是守恒 + 双赢） ============

/-
  【交易的本质：互补填洞，总量守恒，双方受益】

  交易不是"你赢我输"（零和），是"互补"——你的有填我的洞，我的有填你的洞。
  交换前后总"有"量不变（D7），双方的洞都被填满（双赢）。

  这就是"以实养虚""水怎么上来的"：高处的水（有）养低处的洞（无），
  总量不增不减，只是从"过剩处"转移到"缺失处"。

  《暹界定理》说"交易的本质在暹界"——互补洞在临界处完成层间转移。
  下面证交易的两个性质：守恒（总量不变）+ 双赢（洞被填 = 死界变生界）。
-/

-- 交易后的持有：x 保留自己的有（[0, m)），洞（[m, max)）被 y 填满。
def traded {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : Fin (max m n) → ℚ :=
  fun i => valOrZero x i + valOrZero y i

-- 交易守恒：交易后 x 的总持有 = x 的有 + y 的有（总量不变，D7）。
theorem traded_conservation {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    (∑ i : Fin (max m n), traded x y i)
      = (∑ i : Fin (max m n), valOrZero x i) + (∑ i : Fin (max m n), valOrZero y i) := by
  unfold traded
  rw [Finset.sum_add_distrib]

-- 交易双赢：交易后 x 在死界（原洞 [m, max)）处的持有 = y 的有（洞被填，x 从无变有）。
theorem traded_gains {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (i : Fin (max m n)) (hi : m ≤ i.val) :
    traded x y i = valOrZero y i := by
  unfold traded
  rw [valOrZero_hole x i hi]
  ring

-- ============ 层间转移：凝结算子 𝒦 与消解算子 ℛ_D ============

/-
  【凝结算子 𝒦 与消解算子 ℛ_D（《暹界定理》）】

  消解算子 ℛ_D（下传/粗化）：把 m 维投影到前 n 维（n ≤ m），丢掉的高维退入盲区（死界）。
  凝结算子 𝒦（上浮/细化）：把 n 维补 0 到 m 维（m ≥ n），补 0 的维是洞（死界），等待上浮填满。

  两者互为逆（《暹界定理》"下传与上浮互为层间读数"）：
    ℛ_D ∘ 𝒦 = 恒等（凝结再消解，n 维内恢复）；
    𝒦 ∘ ℛ_D 在 n 维上恢复原值（消解再凝结，n 维外变洞）。
-/

-- 消解算子 ℛ_D（下传/粗化）：投影到前 n 维（n ≤ m）。
def coarsen {m n : ℕ} (h : n ≤ m) (x : StateQuant m) : StateQuant n :=
  { val := fun i : Fin n => x.val ⟨i.val, lt_of_lt_of_le i.isLt h⟩, phase := x.phase }

-- 凝结算子 𝒦（上浮/细化）：补 0 到 m 维，缺失维 = 洞。
def condense {m n : ℕ} (x : StateQuant n) : StateQuant m :=
  { val := fun i : Fin m => if hi : i.val < n then x.val ⟨i.val, hi⟩ else 0, phase := x.phase }

-- 𝒦 ∘ ℛ_D 的逆（左逆）：凝结再消解 = 恒等（在 n 维）。
theorem coarsen_condense_eq {m n : ℕ} (h : n ≤ m) (x : StateQuant n) :
    coarsen h (condense x) = x := by
  unfold coarsen condense
  cases x
  simp [Fin.eta]

-- ℛ_D ∘ 𝒦 的逆（右逆）：消解再凝结，在 n 维上恢复原值。
theorem condense_coarsen_on_val {m n : ℕ} (h : n ≤ m) (x : StateQuant m) :
    ∀ i : Fin n, (condense (coarsen h x)).val ⟨i.val, lt_of_lt_of_le i.isLt h⟩
      = x.val ⟨i.val, lt_of_lt_of_le i.isLt h⟩ := by
  intro i
  unfold condense coarsen
  simp

-- ============ 差异合成 ⊕_D（D4 公理） ============

/-
  【差异合成 ⊕_D（公理 D4）】

  差异合成不是加法：小差异线性叠加（取 max），大差异非线性跃迁（发散）。
  相变点 τ_c 是差异合成自身的内禀门槛。

  简化到 ℚ 值（差异台阶 λ_i 的读数）：
    · 线性区（两个差异都 < τ_c）：⊕_D = max（线性叠加，逐级累积）；
    · 爆炸区（任一差异 ≥ τ_c）：⊕_D = 和（非线性跃迁，发散）。
-/

-- 差异合成 ⊕_D：线性区取 max，爆炸区取和。
def composeD (τ_c : ℚ) (a b : ℚ) : ℚ :=
  if a < τ_c ∧ b < τ_c then max a b else a + b

-- ============ ⊕_D 四相：幂等分相（线性幂等 / 过载截断 / 混合发散） ============

/-
  【⊕_D 四相 = 熵的四种命运；幂等 = 熵增的停点】

  四相（归隐理论《差异环上的三相/四相》）：
    线性相（ρ ≈ n）       ：a ⊕ b = max（次可加，稳定累积）
    过载相（n < ρ < τ_c） ：a ⊕ b > a + b（超可加，趋向消解）
    爆炸相（ρ < n，s 不足）：a ⊕ b ≫ a + b（发散，趋向散逸）
    饱和相（ρ > τ_c）     ：a ⊕ b → const（截断，归隐盲区）

  这里把 ⊕_D 从两相（composeD：线性 max / 爆炸 +）扩成四相（composeD4）：
    线性相（a,b < τ_c）       ：max a b（次可加）
    饱和相（a,b ≥ τ_c）       ：τ_c（截断，归隐盲区）
    混合相（一个<τ_c 一个≥τ_c）：a + b（发散，趋向消解/散逸）

  幂等分相（关键）：自合成 a ⊕ a 在线性相幂等（max a a = a，稳定），
  在过载相（a > τ_c）不幂等（截断到 τ_c，损失 a − τ_c = 熵增）。
  所以"幂等 = 稳定 = 停点"，"不幂等 = 截断损耗 = 熵增"。
-/

-- 四相差异合成 ⊕_D（D4 四相版）：线性 max / 饱和截断 / 混合和。
def composeD4 (τ_c : ℚ) (a b : ℚ) : ℚ :=
  if a < τ_c ∧ b < τ_c then max a b
  else if τ_c ≤ a ∧ τ_c ≤ b then τ_c
  else a + b

-- ⊕_D 交换（两相版）——注释里引用过但此前没有真实定义，补上。
theorem composeD_comm (τ_c a b : ℚ) : composeD τ_c a b = composeD τ_c b a := by
  unfold composeD
  by_cases h : a < τ_c ∧ b < τ_c
  · simp [h, max_comm]
  · have h' : ¬ (b < τ_c ∧ a < τ_c) := fun hh => h ⟨hh.2, hh.1⟩
    simp [h, h', add_comm]

-- ⊕_D 交换（四相版）。
theorem composeD4_comm (τ_c a b : ℚ) : composeD4 τ_c a b = composeD4 τ_c b a := by
  unfold composeD4
  by_cases h1 : a < τ_c ∧ b < τ_c
  · simp [h1, max_comm]
  · by_cases h2 : τ_c ≤ a ∧ τ_c ≤ b
    · have h1' : ¬ (b < τ_c ∧ a < τ_c) := fun hh => h1 ⟨hh.2, hh.1⟩
      simp [h1, h2, h1']
    · have h1' : ¬ (b < τ_c ∧ a < τ_c) := fun hh => h1 ⟨hh.2, hh.1⟩
      have h2' : ¬ (τ_c ≤ b ∧ τ_c ≤ a) := fun hh => h2 ⟨hh.2, hh.1⟩
      simp [h1, h2, h1', h2', add_comm]

-- 线性相：两个都 < τ_c，取 max（次可加，稳定累积）。
theorem composeD4_linear {τ_c a b : ℚ} (ha : a < τ_c) (hb : b < τ_c) :
    composeD4 τ_c a b = max a b := by
  unfold composeD4
  simp [ha, hb]

-- 饱和相：两个都 ≥ τ_c，截断到 τ_c（归隐盲区）。
theorem composeD4_saturated {τ_c a b : ℚ} (ha : τ_c ≤ a) (hb : τ_c ≤ b) :
    composeD4 τ_c a b = τ_c := by
  unfold composeD4
  have hnot1 : ¬ (a < τ_c ∧ b < τ_c) := by
    intro h; exact not_lt_of_ge ha h.1
  simp [hnot1, ha, hb]

-- 混合相：一个 < τ_c，一个 ≥ τ_c，取和（发散）。
theorem composeD4_mixed {τ_c a b : ℚ} (ha : a < τ_c) (hb : τ_c ≤ b) :
    composeD4 τ_c a b = a + b := by
  unfold composeD4
  have hnot1 : ¬ (a < τ_c ∧ b < τ_c) := by
    intro h; exact not_lt_of_ge hb h.2
  have hnot2 : ¬ (τ_c ≤ a ∧ τ_c ≤ b) := by
    intro h; exact not_lt_of_ge h.1 ha
  simp [hnot1, hnot2]

-- 四相完备（有限性 ⇒ 四相）：composeD4 的输出恰是三种之一（线性 max / 饱和 τ_c / 混合和），
-- 无第四种。τ_c 的台阶恰在 min a b 与 max a b 两处——三分逼出全部相。
theorem composeD4_trichotomy (τ_c a b : ℚ) :
    composeD4 τ_c a b = max a b ∨ composeD4 τ_c a b = τ_c ∨ composeD4 τ_c a b = a + b := by
  unfold composeD4
  by_cases h1 : a < τ_c ∧ b < τ_c
  · left; simp [h1]
  · by_cases h2 : τ_c ≤ a ∧ τ_c ≤ b
    · right; left; simp [h1, h2]
    · right; right; simp [h1, h2]

-- 台阶在 max：max a b < τ_c 时是线性相（τ_c 越过上台阶）。
theorem composeD4_linear_of_max_lt {τ_c a b : ℚ} (h : max a b < τ_c) :
    composeD4 τ_c a b = max a b := by
  unfold composeD4
  have ha : a < τ_c := lt_of_le_of_lt (le_max_left a b) h
  have hb : b < τ_c := lt_of_le_of_lt (le_max_right a b) h
  simp [ha, hb]

-- 台阶在 min：τ_c ≤ min a b 时是饱和相（τ_c 越过下台阶）。
theorem composeD4_saturated_of_le_min {τ_c a b : ℚ} (h : τ_c ≤ min a b) :
    composeD4 τ_c a b = τ_c := by
  unfold composeD4
  have ha : τ_c ≤ a := le_trans h (min_le_left a b)
  have hb : τ_c ≤ b := le_trans h (min_le_right a b)
  have hnot : ¬ (a < τ_c ∧ b < τ_c) := by intro h'; exact not_lt_of_ge ha h'.1
  simp [hnot, ha, hb]

-- ============ ρ 密度版四相（原文《差异环上的三相/四相》） ============

/-
  【ρ 密度版四相：原文的"相"是密度 ρ = s/r 的相，不是输入值的相】

  原文《差异环上的三相/四相》：相态由局部密度 ρ_k = s_k/r_k 与 n、τ_c 决定：
    线性叠加相：ρ ≈ n（|ρ − n| ≤ δ，雪球稳定，结构凝结）
    过载相：n + δ < ρ < τ_c（趋向消解，未饱和）
    差异爆炸相：ρ < n − δ（s 不足，发散，环断裂）
    差异饱和相：τ_c ≤ ρ（截断，归隐，环坍缩）

  composeD4 是"值版"（a、b 相对 τ_c 的三分），只覆盖线性/饱和两个极端；
  这里补上"ρ 密度版"四相——密度 ρ 相对 n、τ_c、δ 的四分，完备无遗漏。
-/

-- 差异密度相态（ρ 版四相）。
inductive DensityPhase where
  | linear     -- 线性叠加相：|ρ − n| ≤ δ（雪球稳定，ρ ≈ n）
  | overload   -- 过载相：n + δ < ρ < τ_c（趋向消解，未饱和）
  | explosive  -- 差异爆炸相：ρ < n − δ（s 不足，发散，环断裂）
  | saturated  -- 差异饱和相：τ_c ≤ ρ（截断，归隐，环坍缩）
  deriving DecidableEq, Inhabited

-- 密度相态判定：ρ 相对 n、τ_c、δ 的四分。
def densityPhase (ρ n τ_c δ : ℚ) : DensityPhase :=
  if |ρ - n| ≤ δ then .linear
  else if ρ < n then .explosive
  else if ρ < τ_c then .overload
  else .saturated

-- 线性相 ⟺ ρ ≈ n（|ρ − n| ≤ δ）。
theorem densityPhase_linear_iff (ρ n τ_c δ : ℚ) :
    densityPhase ρ n τ_c δ = .linear ↔ |ρ - n| ≤ δ := by
  unfold densityPhase
  constructor
  · intro h
    by_cases hle : |ρ - n| ≤ δ
    · exact hle
    · by_cases h2 : ρ < n
      · simp [hle, h2] at h
      · by_cases h3 : ρ < τ_c
        · simp [hle, h2, h3] at h
        · simp [hle, h2, h3] at h
  · intro hle
    simp [hle]

-- 爆炸相 ⟺ ρ 显著小于 n（ρ < n 且不在 n 的 δ 邻域内）。
theorem densityPhase_explosive_iff (ρ n τ_c δ : ℚ) :
    densityPhase ρ n τ_c δ = .explosive ↔ ¬ |ρ - n| ≤ δ ∧ ρ < n := by
  unfold densityPhase
  constructor
  · intro h
    have hnot : ¬ |ρ - n| ≤ δ := by
      intro hle
      simp [hle] at h
    constructor
    · exact hnot
    · by_cases h2 : ρ < n
      · exact h2
      · by_cases h3 : ρ < τ_c
        · simp [hnot, h2, h3] at h
        · simp [hnot, h2, h3] at h
  · intro ⟨hnot, h2⟩
    simp [hnot, h2]

-- 过载相 ⟺ n 的 δ 邻域之外、n ≤ ρ < τ_c。
theorem densityPhase_overload_iff (ρ n τ_c δ : ℚ) :
    densityPhase ρ n τ_c δ = .overload ↔ ¬ |ρ - n| ≤ δ ∧ ¬ ρ < n ∧ ρ < τ_c := by
  unfold densityPhase
  constructor
  · intro h
    have hnot : ¬ |ρ - n| ≤ δ := by
      intro hle
      simp [hle] at h
    have hnlt : ¬ ρ < n := by
      intro h2
      simp [hnot, h2] at h
    constructor
    · exact hnot
    · constructor
      · exact hnlt
      · by_cases h3 : ρ < τ_c
        · exact h3
        · simp [hnot, hnlt, h3] at h
  · intro ⟨hnot, hnlt, h3⟩
    simp [hnot, hnlt, h3]

-- 饱和相 ⟺ ρ ≥ τ_c（且在 n 的 δ 邻域之外）。
theorem densityPhase_saturated_iff (ρ n τ_c δ : ℚ) :
    densityPhase ρ n τ_c δ = .saturated ↔ ¬ |ρ - n| ≤ δ ∧ ¬ ρ < n ∧ ¬ ρ < τ_c := by
  unfold densityPhase
  constructor
  · intro h
    have hnot : ¬ |ρ - n| ≤ δ := by
      intro hle
      simp [hle] at h
    have hnlt : ¬ ρ < n := by
      intro h2
      simp [hnot, h2] at h
    have hntc : ¬ ρ < τ_c := by
      intro h3
      simp [hnot, hnlt, h3] at h
    exact ⟨hnot, hnlt, hntc⟩
  · intro ⟨hnot, hnlt, hntc⟩
    simp [hnot, hnlt, hntc]

-- 四相完备：任意密度 ρ 恰好落在四相之一，无遗漏——四分逼出全部相。
theorem densityPhase_complete (ρ n τ_c δ : ℚ) :
    densityPhase ρ n τ_c δ = .linear ∨ densityPhase ρ n τ_c δ = .overload ∨
    densityPhase ρ n τ_c δ = .explosive ∨ densityPhase ρ n τ_c δ = .saturated := by
  unfold densityPhase
  by_cases h1 : |ρ - n| ≤ δ
  · left; simp [h1]
  · by_cases h2 : ρ < n
    · right; right; left; simp [h1, h2]
    · by_cases h3 : ρ < τ_c
      · right; left; simp [h1, h2, h3]
      · right; right; right; simp [h1, h2, h3]

-- ============ 最小差异原理：差异均匀条件 ρ_k ≈ n ============

/-
  【最小差异原理（原文《最小差异原理》）：最平差异链 = 唯一存活】

  差异链 X₀ ⊕_D … ⊕_D X_m 从 A 到 B，每步局部密度 ρ_k = s_k/r_k。
  原文核心命题：存活链的每一步都必须 ρ_k ≈ n（|ρ_k − n| ≤ δ，落在线性相）。
  不是"最小化"（变分 δS=0），是"唯一存活"——任何一步爆炸（发散）或
  饱和（截断），链在层间传递中断裂，无法闭合（循环幂等）。

  这里把"差异均匀条件"与 ρ 密度四相焊起来：
    均匀（每步 ρ_k ≈ n）⟺ 每步落在线性相 ⟺ 每步不爆炸、不过载、不饱和。
-/

-- 链均匀：每一步密度都 ≈ n（|ρ_k − n| ≤ δ）。
def chainUniform {m : ℕ} (ρ : Fin m → ℚ) (n δ : ℚ) : Prop :=
  ∀ k : Fin m, |ρ k - n| ≤ δ

-- 均匀 ⟺ 每步落在线性相（差异均匀条件 = 密度四相里的线性相）。
theorem chainUniform_iff_all_linear {m : ℕ} (ρ : Fin m → ℚ) (n τ_c δ : ℚ) :
    chainUniform ρ n δ ↔ ∀ k : Fin m, densityPhase (ρ k) n τ_c δ = .linear := by
  unfold chainUniform
  constructor
  · intro h k
    exact (densityPhase_linear_iff (ρ k) n τ_c δ).mpr (h k)
  · intro h k
    exact (densityPhase_linear_iff (ρ k) n τ_c δ).mp (h k)

-- 最小差异原理：链均匀（每步 ρ_k ≈ n）⟺ 每步不爆炸、不过载、不饱和。
-- "最平差异链"是唯一存活——大自然不最小化作用量，只维持雪球平衡。
theorem minimal_difference_principle {m : ℕ} (ρ : Fin m → ℚ) (n τ_c δ : ℚ) :
    chainUniform ρ n δ ↔
      ∀ k : Fin m, densityPhase (ρ k) n τ_c δ ≠ .explosive ∧
                   densityPhase (ρ k) n τ_c δ ≠ .overload ∧
                   densityPhase (ρ k) n τ_c δ ≠ .saturated := by
  unfold chainUniform
  constructor
  · intro h k
    have hlin : densityPhase (ρ k) n τ_c δ = .linear :=
      (densityPhase_linear_iff (ρ k) n τ_c δ).mpr (h k)
    constructor
    · intro he; rw [hlin] at he; cases he
    · constructor
      · intro ho; rw [hlin] at ho; cases ho
      · intro hs; rw [hlin] at hs; cases hs
  · intro h k
    rcases densityPhase_complete (ρ k) n τ_c δ with hlin | hov | hexp | hsat
    · exact (densityPhase_linear_iff (ρ k) n τ_c δ).mp hlin
    · exfalso; exact (h k).2.1 hov
    · exfalso; exact (h k).1 hexp
    · exfalso; exact (h k).2.2 hsat

-- 线性相幂等：稳定节点，自合成回到自己（max a a = a）。
theorem composeD4_linear_idempotent {τ_c a : ℚ} (ha : a < τ_c) :
    composeD4 τ_c a a = a := by
  rw [composeD4_linear ha ha, max_self]

-- 过载截断：a ≥ τ_c 时自合成被截到 τ_c（损失 a − τ_c = 熵增）。
theorem composeD4_overload_truncation {τ_c a : ℚ} (ha : τ_c ≤ a) :
    composeD4 τ_c a a = τ_c := by
  rw [composeD4_saturated ha ha]

-- 过载不幂等：a > τ_c 时自合成 ≠ 自己（截断损耗 = 熵增不可逆）。
theorem composeD4_overload_not_idempotent {τ_c a : ℚ} (ha : τ_c < a) :
    composeD4 τ_c a a ≠ a := by
  have htrunc : composeD4 τ_c a a = τ_c := composeD4_overload_truncation (le_of_lt ha)
  rw [htrunc]
  exact ne_of_lt ha

-- 混合发散：a ⊕ b 当 b ≠ 0 时不回自己（群体异合成发散 = 熵增）。
theorem composeD4_mixed_divergence {τ_c a b : ℚ} (ha : a < τ_c) (hb : τ_c ≤ b) (hb0 : b ≠ 0) :
    composeD4 τ_c a b ≠ a := by
  rw [composeD4_mixed ha hb]
  intro h
  have : b = 0 := by linarith
  exact hb0 this

-- ============ ⊕_D 的代数结构：幂等域、结合区、单位、幽灵 ============

/-
  【⊕_D 作为一个"分段代数"】

  ⊕_D 不是一个普通的二元运算：它在三个区域里分别等于三种不同的运算：

      区域        条件              值           代数身份
      线性相      a, b < τ_c        max a b      max 半格（幂等）
      饱和相      a, b ≥ τ_c        τ_c          常值（幽灵吸收）
      混合相      a < τ_c ≤ b       a + b        加法群（自由加）

  于是它的"代数定律"也是分段的：

    · 幂等：a ⊕ a = a  ⟺  a ≤ τ_c   （只在线性相 + 边界成立）
    · 结合：全线性相成立（= max 结合）、全饱和相成立（= 常数）；
            混合相失败（composeD_not_assoc 的反例就是把两个相切开了）
    · 单位：ℚ 上没有单位元（负元素破坏）；非负 ℚ 上有单位元 0（τ_c > 0）

  这不是环、半环、幺半群——它是**分段**的：每个相有自己的一套定律，
  跨相时定律失效。但它也不是"随便的运算"：三个相内各自是标准代数对象，
  只有"跨相"是新的。这就是 τ_c 作为 **ghost 阈值** 的含义：
  它不参与运算，它决定运算的**相**。
-/

-- 混合相（对称版）：a ≥ τ_c > b。
theorem composeD4_mixed' {τ_c a b : ℚ} (ha : τ_c ≤ a) (hb : b < τ_c) :
    composeD4 τ_c a b = a + b := by
  rw [composeD4_comm, composeD4_mixed hb ha, add_comm]

-- 自合成统一：a ⊕ a = a（线性相 + 边界）或 τ_c（饱和相）。
theorem composeD4_self (τ_c a : ℚ) :
    composeD4 τ_c a a = if a ≤ τ_c then a else τ_c := by
  by_cases ha : a ≤ τ_c
  · rw [ite_eq_left ha]
    rcases lt_or_eq_of_le ha with hlt | heq
    · rw [composeD4_linear hlt hlt, max_self]
    · subst heq
      rw [composeD4_saturated le_rfl le_rfl]
  · rw [ite_eq_right ha]
    have hlt : τ_c < a := not_le.mp ha
    rw [composeD4_saturated (le_of_lt hlt) (le_of_lt hlt)]

-- 幂等域：a ⊕ a = a ⟺ a ≤ τ_c。
theorem composeD4_idem_iff (τ_c a : ℚ) :
    composeD4 τ_c a a = a ↔ a ≤ τ_c := by
  rw [composeD4_self]
  by_cases ha : a ≤ τ_c
  · rw [ite_eq_left ha]
    exact ⟨fun _ => ha, fun _ => rfl⟩
  · rw [ite_eq_right ha]
    constructor
    · intro h
      exact absurd h (ne_of_lt (not_le.mp ha))
    · intro h
      exact absurd h ha

-- 结合区一：全线性相（= max 结合）。
theorem composeD4_assoc_of_lt {τ_c a b c : ℚ} (ha : a < τ_c) (hb : b < τ_c) (hc : c < τ_c) :
    composeD4 τ_c (composeD4 τ_c a b) c = composeD4 τ_c a (composeD4 τ_c b c) := by
  have hablt : max a b < τ_c := max_lt ha hb
  have hbclt : max b c < τ_c := max_lt hb hc
  rw [composeD4_linear ha hb, composeD4_linear hb hc,
      composeD4_linear hablt hc, composeD4_linear ha hbclt, max_assoc]

-- 结合区二：全饱和相（= 常数）。
theorem composeD4_assoc_of_ge {τ_c a b c : ℚ} (ha : τ_c ≤ a) (hb : τ_c ≤ b) (hc : τ_c ≤ c) :
    composeD4 τ_c (composeD4 τ_c a b) c = composeD4 τ_c a (composeD4 τ_c b c) := by
  rw [composeD4_saturated ha hb, composeD4_saturated le_rfl hc,
      composeD4_saturated hb hc, composeD4_saturated ha le_rfl]

-- τ_c 是强区的幽灵吸收元：强元素碰到 τ_c 还是 τ_c。
theorem tau_absorb {τ_c a : ℚ} (ha : τ_c ≤ a) :
    composeD4 τ_c τ_c a = τ_c ∧ composeD4 τ_c a τ_c = τ_c :=
  ⟨composeD4_saturated le_rfl ha, composeD4_saturated ha le_rfl⟩

-- ℚ 上没有单位元：负元素总会破坏。
theorem composeD4_no_unit (τ_c : ℚ) :
    ¬ ∃ e : ℚ, ∀ a : ℚ, composeD4 τ_c e a = a := by
  rintro ⟨e, he⟩
  by_cases hec : e < τ_c
  · have ha : e - 1 < τ_c := by linarith
    have h := he (e - 1)
    rw [composeD4_linear hec ha, max_eq_left (by linarith)] at h
    linarith
  · have he_ge : τ_c ≤ e := le_of_not_gt hec
    by_cases he0 : e = 0
    · rw [he0] at he he_ge
      have h := he 1
      rw [composeD4_saturated (by linarith : τ_c ≤ 0) (by linarith : τ_c ≤ 1)] at h
      linarith
    · have ha : τ_c - 1 < τ_c := by linarith
      have h := he (τ_c - 1)
      rw [composeD4_mixed' he_ge ha] at h
      have hez : e = 0 := by linarith
      exact he0 hez

-- 非负区有单位元 0（τ_c > 0）。
theorem composeD4_unit_nonneg {τ_c : ℚ} (hτ : 0 < τ_c) :
    ∀ a : ℚ, 0 ≤ a → composeD4 τ_c 0 a = a ∧ composeD4 τ_c a 0 = a := by
  intro a ha
  constructor
  · by_cases hlt : a < τ_c
    · rw [composeD4_linear hτ hlt, max_eq_right ha]
    · rw [composeD4_mixed hτ (le_of_not_gt hlt)]
      ring
  · by_cases hlt : a < τ_c
    · rw [composeD4_linear hlt hτ, max_eq_left ha]
    · rw [composeD4_mixed' (le_of_not_gt hlt) hτ]
      ring

-- 满射：τ_c > 0 时，任何 ℚ 都是某个合成的结果。
theorem composeD4_surjective {τ_c : ℚ} (hτ : 0 < τ_c) :
    Function.Surjective (fun p : ℚ × ℚ => composeD4 τ_c p.1 p.2) := by
  intro y
  by_cases hy : y < τ_c
  · exact ⟨(y, y), by
      show composeD4 τ_c y y = y
      rw [composeD4_linear hy hy, max_self]⟩
  · have hy' : τ_c ≤ y := le_of_not_gt hy
    refine ⟨(y, 0), ?_⟩
    show composeD4 τ_c y 0 = y
    rw [composeD4_mixed' hy' hτ]
    ring

-- 【分段代数总纲】⊕_D 的完整代数画像。
theorem segmented_algebra (τ_c : ℚ) :
    -- (a) 三个相内各自是标准运算
    (∀ a b, a < τ_c → b < τ_c → composeD4 τ_c a b = max a b) ∧
    (∀ a b, τ_c ≤ a → τ_c ≤ b → composeD4 τ_c a b = τ_c) ∧
    (∀ a b, a < τ_c → τ_c ≤ b → composeD4 τ_c a b = a + b) ∧
    -- (b) 幂等域 = 线性相 + 边界
    (∀ a, composeD4 τ_c a a = a ↔ a ≤ τ_c) ∧
    -- (c) 两个结合区
    (∀ a b c, a < τ_c → b < τ_c → c < τ_c →
      composeD4 τ_c (composeD4 τ_c a b) c = composeD4 τ_c a (composeD4 τ_c b c)) ∧
    (∀ a b c, τ_c ≤ a → τ_c ≤ b → τ_c ≤ c →
      composeD4 τ_c (composeD4 τ_c a b) c = composeD4 τ_c a (composeD4 τ_c b c)) ∧
    -- (d) τ_c 是强区的幽灵吸收元
    (∀ a, τ_c ≤ a → composeD4 τ_c τ_c a = τ_c) ∧
    -- (e) ℚ 上无单位元
    (¬ ∃ e : ℚ, ∀ a : ℚ, composeD4 τ_c e a = a) ∧
    -- (f) τ_c > 0 时非负区有单位元 0
    (0 < τ_c → ∀ a : ℚ, 0 ≤ a →
      composeD4 τ_c 0 a = a ∧ composeD4 τ_c a 0 = a) :=
  ⟨fun _ _ => composeD4_linear,
   fun _ _ => composeD4_saturated,
   fun _ _ => composeD4_mixed,
   fun _ => composeD4_idem_iff τ_c _,
   fun _ _ _ => composeD4_assoc_of_lt,
   fun _ _ _ => composeD4_assoc_of_ge,
   fun _ ha => (tau_absorb ha).1,
   composeD4_no_unit τ_c,
   fun h => composeD4_unit_nonneg h⟩

-- ============ 循环幂等 ⊕_D^(m)：线性闭合 / 过载截断 ============

/-
  【循环幂等 ⊕_D^(m) = id_δ：全局闭合 = 熵增的全局停点】

  循环幂等（归隐理论《差异环上的雪球》联动 4）：绕环一周的合成步数 m 满足
  全局差异守恒（D7），即 m 步合成后回到自己。局部稳定（s/r = n）+ 全局闭合
  （循环幂等）= 存在。

  ⊕_D 不结合（composeD_not_assoc），所以 ⊕_D^(m) 需约定括号——这里取左结合。
  幂等的本质是 max：线性相 ⊕_D = max，而 max 幂等（max a a = a），
  所以线性相下任意次自合成闭合（= a）。过载相 ⊕_D = 截断（τ_c），
  一次以上自合成被截到 τ_c（损失 = 熵增）。
-/

-- m 次自合成（左结合）：a ⊕ a ⊕ ... ⊕ a（m 次）。
def composeD4_selfpow (τ_c a : ℚ) : ℕ → ℚ
  | 0 => a
  | m+1 => composeD4 τ_c (composeD4_selfpow τ_c a m) a

-- 线性相闭合：a < τ_c 时，任意次自合成 = a（幂等 = 循环闭合 = 稳定）。
theorem composeD4_selfpow_linear {τ_c a : ℚ} (ha : a < τ_c) (m : ℕ) :
    composeD4_selfpow τ_c a m = a := by
  induction m with
  | zero => rfl
  | succ m ih =>
      unfold composeD4_selfpow
      rw [ih, composeD4_linear_idempotent ha]

-- 过载相截断：a ≥ τ_c 时，一次以上自合成被截到 τ_c（损失 a − τ_c = 熵增）。
theorem composeD4_selfpow_overload {τ_c a : ℚ} (ha : τ_c ≤ a) (m : ℕ) (hm : 0 < m) :
    composeD4_selfpow τ_c a m = τ_c := by
  induction m with
  | zero => cases (Nat.not_lt_zero 0 hm)
  | succ m ih =>
      unfold composeD4_selfpow
      by_cases h0 : m = 0
      · subst h0
        change composeD4 τ_c a a = τ_c
        rw [composeD4_saturated ha ha]
      · have hself : composeD4_selfpow τ_c a m = τ_c := ih (Nat.pos_of_ne_zero h0)
        rw [hself]
        exact composeD4_saturated (le_refl τ_c) ha

-- 环 C_m 绕环一周（左结合）：a 0 ⊕ a 1 ⊕ ... ⊕ a (m-1)。
def cycleCompose (τ_c : ℚ) : (m : ℕ) → (Fin m → ℚ) → ℚ
  | 0, _ => 0
  | m+1, a => composeD4 τ_c (cycleCompose τ_c m (fun i : Fin m => a ⟨i.val, lt_trans i.isLt (Nat.lt_succ_self m)⟩)) (a ⟨m, Nat.lt_succ_self m⟩)

-- 线性相下，绕环一周的结果仍在线性相内（max 所有节点 < τ_c）。
theorem cycleCompose_lt {τ_c : ℚ} {m : ℕ} (a : Fin m → ℚ) (hm : 0 < m) (hτ : 0 < τ_c)
    (hlin : ∀ i : Fin m, a i < τ_c) :
    cycleCompose τ_c m a < τ_c := by
  induction m with
  | zero => cases (Nat.not_lt_zero 0 hm)
  | succ m ih =>
      unfold cycleCompose
      have hprev : cycleCompose τ_c m (fun i : Fin m => a ⟨i.val, lt_trans i.isLt (Nat.lt_succ_self m)⟩) < τ_c := by
        by_cases h0 : m = 0
        · subst h0
          unfold cycleCompose
          exact hτ
        · exact ih (fun i : Fin m => a ⟨i.val, lt_trans i.isLt (Nat.lt_succ_self m)⟩) (Nat.pos_of_ne_zero h0) (fun i => hlin ⟨i.val, lt_trans i.isLt (Nat.lt_succ_self m)⟩)
      have hlast : a ⟨m, Nat.lt_succ_self m⟩ < τ_c := hlin ⟨m, Nat.lt_succ_self m⟩
      rw [composeD4_linear hprev hlast]
      exact max_lt hprev hlast

-- 线性相循环幂等：绕环一周的结果再自合成 = 自己（全局闭合 = 稳定）。
theorem cycleCompose_linear_idempotent {τ_c : ℚ} {m : ℕ} (a : Fin m → ℚ) (hm : 0 < m) (hτ : 0 < τ_c)
    (hlin : ∀ i : Fin m, a i < τ_c) :
    composeD4 τ_c (cycleCompose τ_c m a) (cycleCompose τ_c m a) = cycleCompose τ_c m a := by
  exact composeD4_linear_idempotent (cycleCompose_lt a hm hτ hlin)

-- 常值环幂等：线性相下，常值环（所有节点 = h）绕环一周 = h。
-- 这是"绕环两圈 = 绕环一圈"的精确形式：第二圈是常值环（每节点都已是 h），绕回 h 不变。
theorem cycleCompose_const {τ_c : ℚ} {m : ℕ} (h : ℚ) (hm : 0 < m) (hh0 : 0 ≤ h) (hh : h < τ_c) :
    cycleCompose τ_c m (fun _ : Fin m => h) = h := by
  induction m with
  | zero => cases (Nat.not_lt_zero 0 hm)
  | succ m ih =>
      unfold cycleCompose
      by_cases h0 : m = 0
      · subst h0
        unfold cycleCompose
        have hτ0 : 0 < τ_c := by linarith [hh0, hh]
        rw [composeD4_linear hτ0 hh]
        exact max_eq_right hh0
      · have hprev : cycleCompose τ_c m (fun _ : Fin m => h) = h := ih (Nat.pos_of_ne_zero h0)
        rw [hprev]
        exact composeD4_linear_idempotent hh

-- ============ 主副轨迹与税台（原文《差异环构造》二、三节） ============

/-
  【主轨迹 / 副轨迹 / 税台】

  环 C_m 有 m 条边。主轨迹从 0 号边向前累积，副轨迹从 m−1 号边向后累积：
      主(k) 吃边 {0, …, k−1}
      副(k) 吃边 {m−k, …, m−1}

  两轨迹的边集在环的半程处**互补**——这就是"税台在环的半程处交汇"。

  奇偶分岔（原文的核心洞察）：
    · m 偶：k = m/2 时，主副轨迹**完美二分**（不重不漏，对径节点对）；
    · m 奇：k = (m−1)/2 时，中间**恰剩一条边**——这条边就是税台。
  换句话说：**税台是环的反射 k ↦ m−1−k 的不动点**。
  奇数环有唯一自反点（税台），偶数环全是两两对径、没有自反点。

  这与"自我 = reflect 的不动点"是同一个结构：
  **税台之于环的反射，正如自我之于冻结的自反**——两者都是"反射的唯一驻留处"。
-/

-- 主轨迹吃掉的边索引集（前 k 条）。
def mainEdges (_m k : ℕ) : Finset ℕ := Finset.range k

-- 副轨迹吃掉的边索引集（后 k 条）。
def subEdges (m k : ℕ) : Finset ℕ := Finset.Ico (m - k) m

-- 主副轨迹边集不交（2k ≤ m 时）。
theorem mainEdges_disjoint_subEdges {m k : ℕ} (h : 2 * k ≤ m) :
    Disjoint (mainEdges m k) (subEdges m k) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  unfold mainEdges at hx
  unfold subEdges at hx'
  rw [Finset.mem_range] at hx
  rw [Finset.mem_Ico] at hx'
  omega

-- 偶数环：半程处主副轨迹完美二分（不重不漏，覆盖全环）。
theorem tax_cross_even {m : ℕ} (hm : m % 2 = 0) :
    mainEdges m (m/2) ∪ subEdges m (m/2) = Finset.range m := by
  unfold mainEdges subEdges
  ext x
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  omega

-- 奇数环：半程处主副轨迹之外恰剩一条边——税台。
theorem tax_cross_odd {m : ℕ} (hm : m % 2 = 1) :
    (Finset.range m) \ (mainEdges m (m/2) ∪ subEdges m (m/2)) = {m/2} := by
  unfold mainEdges subEdges
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · intro hx
    subst hx
    omega

-- 税台 = 环的反射 k ↦ m−1−k 的不动点：奇数环有唯一不动点，偶数环没有。
theorem ring_reflection_fixed {m : ℕ} (hm : 0 < m) :
    (∃ k : Fin m, m - 1 - k.val = k.val) ↔ m % 2 = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    have hklt : k.val < m := k.isLt
    omega
  · intro hodd
    refine ⟨⟨(m - 1) / 2, by omega⟩, ?_⟩
    show m - 1 - (m - 1) / 2 = (m - 1) / 2
    have hm1 : (m - 1) % 2 = 0 := by omega
    omega

-- ============ 驻留层（Stasis）：不动点的两种形态 ============

/-
  【驻留：税台与自我是同一件事的两种形态】

  差异论里有两处"唯一驻留处"：

    · 环上的税台：反射 k ↦ m−1−k 的**不动点**。反射是**对合**（两次回到原处）。
      存在性由奇偶决定：奇数环必有（唯一），偶数环全无。

    · 库里的自我：`reflect` 的**不动点**（s/r = n）。reflect 是**投影**
      （做两次 = 做一次，幂等），不是对合。

  两种自映射，两种不动点。下面的通用定理说明为什么"奇偶决定存在"：

    **奇数大小的有限集上，任何对合必有不动点。**

  因为非不动点在 `f` 下两两配对，故 |α| ≡ |不动点| (mod 2)。
  |α| 奇 ⟹ |不动点| 奇 ⟹ 至少有一个。
  这解释了"税台永远矗立"——只要环是奇数圈。
-/

-- 驻留点：自映射 step 下不动的点。
def IsStasis {α : Type*} (step : α → α) (x : α) : Prop := step x = x

-- 驻留点集。
noncomputable def stasisSet {α : Type*} [Fintype α] [DecidableEq α] (step : α → α) : Finset α :=
  Finset.univ.filter (fun x => step x = x)

-- 【核心定理】奇数大小的有限线性序上，任何对合必有不动点。
theorem exists_fixed_of_odd_card {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (f : α → α) (hinv : ∀ x, f (f x) = x) (hodd : Odd (Fintype.card α)) :
    ∃ x, f x = x := by
  by_contra h
  push Not at h
  -- 取每对 {x, f x} 中较小的一个作代表
  set S : Finset α := Finset.univ.filter (fun x => x < f x) with hS
  have hcover : (Finset.univ : Finset α) = S ∪ S.image f := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, true_and, hS, Finset.mem_filter,
      Finset.mem_image]
    constructor
    · intro _
      by_cases hx : x < f x
      · exact Or.inl hx
      · right
        have hxf : f x < x := by
          rcases lt_trichotomy (f x) x with h' | h' | h'
          · exact h'
          · exact absurd h' (h x)
          · exact absurd h' hx
        exact ⟨f x, by rw [hinv]; exact hxf, hinv x⟩
    · rintro (hx | ⟨y, _, _⟩) <;> trivial
  have hdisj : Disjoint S (S.image f) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hS, Finset.mem_filter] at hx
    rw [Finset.mem_image] at hx'
    obtain ⟨y, hy, hfy⟩ := hx'
    rw [hS, Finset.mem_filter] at hy
    have h1 : x < f x := hx.2
    rw [← hfy, hinv y] at h1
    exact absurd h1 (not_lt.mpr (le_of_lt hy.2))
  have himg : (S.image f).card = S.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    have := congrArg f hab
    rwa [hinv, hinv] at this
  have hcard : Fintype.card α = 2 * S.card := by
    rw [show Fintype.card α = (Finset.univ : Finset α).card from rfl, hcover,
      Finset.card_union_of_disjoint hdisj, himg]
    ring
  rw [hcard] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

-- 环的反射（k ↦ m−1−k）是清晰的对合特例：奇数环必有税台。
def ringReflect (m : ℕ) : Fin m → Fin m :=
  fun k => ⟨m - 1 - k.val, by have := k.isLt; omega⟩

theorem ringReflect_involutive {m : ℕ} (_hm : 0 < m) :
    ∀ k : Fin m, ringReflect m (ringReflect m k) = k := by
  intro k
  apply Fin.ext
  show m - 1 - (m - 1 - k.val) = k.val
  have := k.isLt
  omega

-- 由通用定理重得"奇数环必有税台"。
theorem ringReflect_fixed_of_odd {m : ℕ} (hm : 0 < m) (hodd : Odd m) :
    ∃ k : Fin m, ringReflect m k = k :=
  exists_fixed_of_odd_card (ringReflect m) (ringReflect_involutive hm)
    (by simpa using hodd)

-- （自我的驻留见后面 DifferenceObject 一节：self_stasis_iff）

-- ============ 负指数：1/2 就是 2 的 −1 次幂 ============

/-
  【半值 = 2 的负一次幂：分辨率可以"退"，但不能"开方"】

  2^n 是分辨空间的大小。允许负指数就得到 2^(−1) = 1/2、2^(−2) = 1/4 …，
  这些全在 ℚ 里——它们对应"分辨率退一层、退两层"（消解）。
  所以 **半值（暹界临界 1/2）就是"退一层分辨率"**。

  但允许**分数**指数就出了 ℚ：2^(1/2) = √2 ∉ ℚ。
  所以"半维 / 开方分辨率"在差异论里不存在——这正是拒绝连续统的边界。

  而 √(−1) = i 更远：ℚ 里连平方等于 −1 的数都没有（平方恒非负）。
  于是"虚数"标记的不是某种新结构，而是**理论停下脚步的地方**：
  负指数（消解）可以，分数指数（半维）不行，负数开方（虚）更不行。
-/

-- 半值 = 2 的负一次幂。
theorem half_value_is_neg_pow : (1 / 2 : ℚ) = (2 : ℚ) ^ (-(1 : ℤ)) := by
  norm_num [zpow_neg]

-- 负二次幂 = 四分之一（分辨退两层）。
theorem quarter_is_neg_pow : (1 / 4 : ℚ) = (2 : ℚ) ^ (-(2 : ℤ)) := by
  norm_num [zpow_neg]

-- 分辨率"开方"出界：ℚ 里没有 √2（半维不存在）。
theorem no_rational_sqrt_two : ¬ ∃ q : ℚ, q * q = 2 := by
  rw [Rat.exists_mul_self]
  have h2 : Rat.sqrt (2 : ℚ) = 1 := by
    rw [Rat.sqrt_ofNat, Nat.sqrt_two]
    norm_num
  rw [h2]
  norm_num

-- 更远一步：ℚ 里没有 √(−1)（虚数不在差异论内部）。
theorem no_rational_sqrt_neg_one : ¬ ∃ q : ℚ, q * q = -1 := by
  rintro ⟨q, hq⟩
  have h := sq_nonneg q
  nlinarith

-- ============ 半转的三重边界：负指数 / 虚数 / 税台 ============

/-
  【半转（half-turn）在三种结构里的三种命运】

  1/2 = 2^(−1)、i² = −1、e^{iπ} = −1 —— 这三条说的是同一件事：
  **"半转"在不同结构里的形态**。

    · 指数上的半转（负指数）：把乘法翻成倒数。2^(−1) = 1/2，**在 ℚ 内完成**。
      本质：n ↦ 2^n 是加法群 ℤ 到乘法群 ℚ^× 的**同态**，负指数就是"取逆"。
      这也是 e^x 的离散版（e^{x+y} = e^x e^y 正是同态性质）。

    · 乘法上的半转（虚数）：i² = −1，把"平方"翻成"取反"。**ℚ 内无解**——
      平方恒非负，所以 ℚ 的乘法群里没有"半转元素"。

    · 几何上的半转（环反射）：k ↦ m−1−k。**奇数环有唯一不动点（税台），偶数环全无**。

  三者对照恰好定位差异论：
  ℚ 有"指数半转"（消解／负指数），没有"乘法半转"（虚数），
  所以几何半转只能以"不动点"（税台）出现，不能以"乘性元素"（i）出现。

  这就是为什么差异论的"圆"是有限环 C_m 而不是 S¹：
  S¹ 靠 i 闭合（e^{iπ} = −1），C_m 靠税台闭合（反射不动点）。
-/

-- 指数是加法群到乘法群的同态（e^x 与 2^n 的共同本质）。
theorem two_pow_add_zpow (m n : ℤ) : (2 : ℚ) ^ (m + n) = (2 : ℚ) ^ m * (2 : ℚ) ^ n :=
  zpow_add₀ (by norm_num) m n

-- 负指数 = 取逆（"指数上的半转"在 ℚ 内完成）。
theorem two_pow_neg_eq_inv (n : ℤ) : (2 : ℚ) ^ (-n) = ((2 : ℚ) ^ n)⁻¹ :=
  zpow_neg (2 : ℚ) n

-- 【半转的三重边界】三种结构里的"半转"，三种命运。
theorem half_turn_trichotomy :
    -- ① 指数半转：负指数 = 取逆（ℚ 内完成）
    (∀ n : ℤ, (2 : ℚ) ^ (-n) = ((2 : ℚ) ^ n)⁻¹) ∧
    -- ② 乘法半转：虚数（i² = −1）在 ℚ 内不存在
    (¬ ∃ q : ℚ, q * q = -1) ∧
    -- ③ 几何半转：环反射在奇数环上有不动点（税台）
    (∀ m : ℕ, 0 < m → Odd m → ∃ k : Fin m, ringReflect m k = k) :=
  ⟨two_pow_neg_eq_inv, no_rational_sqrt_neg_one,
   fun m hm hodd => ringReflect_fixed_of_odd (m := m) hm hodd⟩

-- ============ 半转合图：三副面孔 = 同一个"关于中心的反射" ============

/-
  【三副面孔，一个动作】

  ① 符号半转：x ↦ −x（相位上乘 −1 = 相消），关于中心 0 的反射。
  ② 指数半转：n ↦ −n（2^(−n) = (2^n)⁻¹），同是关于中心 0 的反射，
     经同态 2^(·) 翻成乘法取逆。
  ③ 几何半转：k ↦ m−1−k（环反射），是关于中心 (m−1)/2 的反射。

  统一的法则只有一条：

      反射 x ↦ c − x 的不动点 ⟺ x = c/2（"中心之半"）。

  于是三副面孔的差别不在动作，而在**中心能否落在空间里**：

    · ① 中心 0 ∈ ℚ —— 不动点是 0，即中性 / 正交（无相位处）；
    · ② 中心 0 ∈ ℤ —— 指数 0，即 2^0 = 1（乘法单位，整圈）；
    · ③ 中心 (m−1)/2 ∈ ℤ ⟺ m 奇 —— 税台存在；m 偶时中心是**半整数**，
      落在两个格点**之间**，无处驻留：这就是"暹界"（半值）在离散环上的形态。

  所以"半转"不是比喻：它是一个统一的反射族，
  奇偶决定的不是转不转，而是**转轴落不落在格点上**。
-/

-- 关于中心 c 的反射：x ↦ c − x。
def reflectAbout (c x : ℚ) : ℚ := c - x

-- 反射是对合。
theorem reflectAbout_involutive (c x : ℚ) : reflectAbout c (reflectAbout c x) = x := by
  unfold reflectAbout
  ring

-- 【统一法则】反射的不动点 = 中心的一半。
theorem reflectAbout_fixed_iff (c x : ℚ) : reflectAbout c x = x ↔ x = c / 2 := by
  unfold reflectAbout
  constructor
  · intro h
    linarith
  · intro h
    subst h
    ring

-- 任何两点都由"以二者之和为中心的半转"互换。
theorem reflectAbout_midpoint (x y : ℚ) : reflectAbout (x + y) x = y := by
  unfold reflectAbout
  ring

-- ① 符号半转 = 关于 0 的反射（相位乘 −1 就是 x ↦ 0 − x）。
theorem neg_eq_reflectAbout_zero (x : ℚ) : -x = reflectAbout 0 x := by
  unfold reflectAbout
  ring

-- ① 的驻留：符号半转的唯一不动点是 0（中性 / 正交）。
theorem sign_neg_fixed_iff (x : ℚ) : -x = x ↔ x = 0 := by
  constructor <;> intro h <;> linarith

-- ③ 环反射在 ℤ 上就是关于 (m−1)/2 的反射。
theorem ringReflect_val (m : ℕ) (k : Fin m) :
    ((ringReflect m k).val : ℤ) = (m : ℤ) - 1 - (k.val : ℤ) := by
  have hk : k.val ≤ m - 1 := by have := k.isLt; omega
  have hm1 : 1 ≤ m := by have := k.isLt; omega
  show ((m - 1 - k.val : ℕ) : ℤ) = (m : ℤ) - 1 - (k.val : ℤ)
  rw [Nat.cast_sub hk, Nat.cast_sub hm1]
  simp

-- ③ 税台的不动点条件 = 反射方程 2k = m−1（ℤ 上）。
theorem ringReflect_fixed_iff_int (m : ℕ) (k : Fin m) :
    ringReflect m k = k ↔ 2 * (k.val : ℤ) = (m : ℤ) - 1 := by
  constructor
  · intro h
    have hv : ((ringReflect m k).val : ℤ) = (k.val : ℤ) := by
      have := congrArg (fun j : Fin m => (j.val : ℤ)) h
      simpa using this
    have h2 := ringReflect_val m k
    linarith
  · intro h
    apply Fin.ext
    have h2 := ringReflect_val m k
    have hv : ((ringReflect m k).val : ℤ) = (k.val : ℤ) := by linarith
    exact_mod_cast hv

-- ③ 奇数环：反射中心落在整数点。
theorem odd_center_integer {m : ℕ} (hm : Odd m) : ∃ k : ℤ, 2 * k = (m : ℤ) - 1 := by
  obtain ⟨t, rfl⟩ := hm
  exact ⟨(t : ℤ), by push_cast; ring⟩

-- ③ 偶数环：反射中心是半整数，ℤ 上无解（无处驻留）。
theorem even_center_no_integer {m : ℕ} (hm : Even m) : ¬ ∃ k : ℤ, 2 * k = (m : ℤ) - 1 := by
  rintro ⟨k, hk⟩
  obtain ⟨t, rfl⟩ := hm
  push_cast at hk
  omega

-- ③ 奇数环：中心本身就是整数（税台所在点）。
theorem odd_center_eq_int {m : ℕ} (hm : Odd m) :
    ∃ t : ℤ, ((m : ℚ) - 1) / 2 = (t : ℚ) := by
  obtain ⟨t, rfl⟩ := hm
  exact ⟨(t : ℤ), by push_cast; ring⟩

-- ③ 偶数环：中心是"整数 + 1/2"，正好卡在两个格点之间（暹界/半值）。
theorem even_center_eq_half {m : ℕ} (hm : Even m) :
    ∃ t : ℤ, ((m : ℚ) - 1) / 2 = (t : ℚ) + 1 / 2 := by
  obtain ⟨t, rfl⟩ := hm
  refine ⟨(t : ℤ) - 1, ?_⟩
  push_cast
  ring

-- 税台存在 ⟺ 环奇（与中心落格是同一条奇偶律的两面）。
theorem tax_iff_center_integer {m : ℕ} (hm : 0 < m) :
    (∃ k : Fin m, ringReflect m k = k) ↔ Odd m := by
  have h1 : (∃ k : Fin m, ringReflect m k = k) ↔ (∃ k : Fin m, m - 1 - k.val = k.val) := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := congrArg Fin.val hk
      simpa [ringReflect] using this
    · rintro ⟨k, hk⟩
      refine ⟨k, Fin.ext ?_⟩
      show m - 1 - k.val = k.val
      exact hk
  rw [h1, ring_reflection_fixed hm]
  exact Nat.odd_iff.symm

-- 【合图定理】三副面孔 + 一条统一法则：半转 = 中心反射，驻留 ⟺ 中心落格。
theorem half_turn_three_faces :
    -- ⓪ 相位上的半转：相消 ⟺ 相位符号之积 = −1（恰好一次半转）
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ), commonDist x y ≤ δ →
      (D x y δ = .destructive ↔ phaseSign x.phase * phaseSign y.phase = -1)) ∧
    -- 统一法则：反射不动点 = 中心之半
    (∀ c x : ℚ, reflectAbout c x = x ↔ x = c / 2) ∧
    -- ① 符号半转 = 中心 0 的反射，唯一不动点 0（中性/正交）
    (∀ x : ℚ, -x = reflectAbout 0 x) ∧
    (∀ x : ℚ, -x = x ↔ x = 0) ∧
    -- ② 指数半转 = 加法反射，经同态翻成乘法取逆
    (∀ n : ℤ, (2 : ℚ) ^ (-n) = ((2 : ℚ) ^ n)⁻¹) ∧
    -- ③ 环半转 = 中心 (m−1)/2 的反射；税台存在 ⟺ 中心落格 ⟺ m 奇
    (∀ m (k : Fin m), ((ringReflect m k).val : ℤ) = (m : ℤ) - 1 - (k.val : ℤ)) ∧
    (∀ m : ℕ, 0 < m → ((∃ k : Fin m, ringReflect m k = k) ↔ Odd m)) ∧
    -- 奇数：中心是整数点；偶数：中心是半整数（暹界），无驻留
    (∀ m : ℕ, Odd m → ∃ t : ℤ, ((m : ℚ) - 1) / 2 = (t : ℚ)) ∧
    (∀ m : ℕ, Even m → ∃ t : ℤ, ((m : ℚ) - 1) / 2 = (t : ℚ) + 1 / 2) :=
  ⟨fun x y δ h => destructive_iff_halfturn x y δ h,
   reflectAbout_fixed_iff, neg_eq_reflectAbout_zero, sign_neg_fixed_iff,
   two_pow_neg_eq_inv, ringReflect_val,
   fun m hm => tax_iff_center_integer (m := m) hm,
   fun _ hm => odd_center_eq_int hm, fun _ hm => even_center_eq_half hm⟩

-- ============ 接轨定理：组合 m 重对称 ↔ ℚ 的乘法旋转 ============

/-
  【接轨：环的组合对称 vs 域的乘法对称】

  环 C_m 有 m 重旋转（组合置换 k ↦ k+1 mod m）。
  若想让它"代数地"实现——即用乘法把旋转变成数 q^k——就需要 ℚ 的 m 次单位根。
  但 ℚ 里只有 ±1：

      q^n = 1 ⟹ q = 1 或 q = -1.

  于是环的 m 重旋转在 ℚ 上**只看得见两阶**：恒等与取反。
  m ≥ 3 时，旋转群被压平成 {1, −1}——"三分之一圈"、"四分之一圈"全部消失。

  **这解释了差异环为什么是"组合环"而不是"代数环"**：
  它的对称性活在 Fin m 的置换里，不活在 ℚ 的乘法里。
  也解释了为什么"半转"（−1）是 ℚ 里唯一非平凡的可实现旋转——
  所以税台（半转的不动点）成了唯一可能的驻留结构。

  这是"接轨"的一个范例：两个结构（组合的环 / 代数的域）一接触，
  一边完整、一边残缺，残缺的那半边**就是差异论的定义域**。
-/

-- ℚ 的单位根只有 ±1（乘法旋转只有整圈和半圈）。
theorem rat_pow_eq_one {q : ℚ} {n : ℕ} (hn : 0 < n) (h : q ^ n = 1) :
    q = 1 ∨ q = -1 := by
  have habs : |q| ^ n = 1 := by rw [← abs_pow, h, abs_one]
  have hnonneg : (0 : ℚ) ≤ |q| := abs_nonneg q
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hone : |q| = 1 := by
    rcases lt_trichotomy |q| 1 with hlt | heq | hgt
    · have := pow_lt_one₀ hnonneg hlt hne
      rw [habs] at this
      linarith
    · exact heq
    · have := one_lt_pow₀ hgt hne
      rw [habs] at this
      linarith
  rwa [abs_eq (by norm_num : (0 : ℚ) ≤ 1)] at hone

-- 没有三等分旋转：q³ = 1 在 ℚ 里只可能是 q = 1（1 的立方根全在 ℂ 里）。
theorem rat_no_third_rotation (q : ℚ) (h : q ^ 3 = 1) : q = 1 := by
  rcases rat_pow_eq_one (by norm_num : 0 < 3) h with h1 | h1
  · exact h1
  · rw [h1] at h
    norm_num at h

-- 【接轨定理】m 重旋转在 ℚ 上只看得见两阶：任何单位根只能是 ±1。
theorem rotation_collapses_to_halfturn {q : ℚ} {n : ℕ} (hn : 0 < n) (h : q ^ n = 1) :
    q = 1 ∨ q = -1 :=
  rat_pow_eq_one hn h

-- 奇数阶旋转在 ℚ 里完全不存在（除恒等）：q^m = 1、m 奇且 ≥ 3 ⟹ q = 1。
theorem rat_no_odd_rotation (q : ℚ) {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m) (h : q ^ m = 1) :
    q = 1 := by
  rcases rat_pow_eq_one (by omega) h with h1 | h1
  · exact h1
  · rw [h1] at h
    have hneg : (-1 : ℚ) ^ m = -1 := Odd.neg_one_pow hodd
    rw [hneg] at h
    linarith

-- 【接轨定理·综合】同一个"奇数"条件，在几何与代数两侧给出完全不同的结论：
-- 几何侧：奇数环有税台（反射不动点）；代数侧：奇数阶无乘法旋转（ℚ 里只有恒等）。
theorem interface_odd_dual :
    -- 几何侧：奇数环上有税台
    (∀ m : ℕ, 0 < m → Odd m → ∃ k : Fin m, ringReflect m k = k) ∧
    -- 代数侧：奇数阶（≥3）的乘法旋转在 ℚ 里只有恒等
    (∀ q : ℚ, ∀ m : ℕ, 3 ≤ m → Odd m → q ^ m = 1 → q = 1) :=
  ⟨fun m hm hodd => ringReflect_fixed_of_odd (m := m) hm hodd,
   fun q _m hm hodd h => rat_no_odd_rotation q hm hodd h⟩

-- ============ 奶淇淋乘法 μ：轨迹对的逐点 ⊕_D ============

/-
  【奶淇淋 μ = ⊕_D 在轨迹对上的逐点提升】

  μ(D₁, D₂)(k) = D₁(k) ⊕_D D₂(k)。
  满足原文两条性质：
    · 对称：μ(D₁,D₂) = μ(D₂,D₁)（税台处主副不可分离，交换不产生新东西）；
    · 幂等（线性相）：μ(μ, μ) = μ（压合一次就到位）。
-/

-- 奶淇淋乘法：轨迹对的逐点 ⊕_D。
def creamMul (τ_c : ℚ) (D₁ D₂ : ℕ → ℚ) : ℕ → ℚ :=
  fun k => composeD4 τ_c (D₁ k) (D₂ k)

-- μ 对称。
theorem creamMul_comm (τ_c : ℚ) (D₁ D₂ : ℕ → ℚ) :
    creamMul τ_c D₁ D₂ = creamMul τ_c D₂ D₁ := by
  funext k
  exact composeD4_comm τ_c (D₁ k) (D₂ k)

-- μ 幂等（线性相）：压合一次就到位。
theorem creamMul_idempotent {τ_c : ℚ} {D₁ D₂ : ℕ → ℚ}
    (h1 : ∀ k, D₁ k < τ_c) (h2 : ∀ k, D₂ k < τ_c) :
    creamMul τ_c (creamMul τ_c D₁ D₂) (creamMul τ_c D₁ D₂) = creamMul τ_c D₁ D₂ := by
  funext k
  have hk : composeD4 τ_c (D₁ k) (D₂ k) = max (D₁ k) (D₂ k) := composeD4_linear (h1 k) (h2 k)
  show composeD4 τ_c (composeD4 τ_c (D₁ k) (D₂ k)) (composeD4 τ_c (D₁ k) (D₂ k))
      = composeD4 τ_c (D₁ k) (D₂ k)
  rw [hk, composeD4_linear (max_lt (h1 k) (h2 k)) (max_lt (h1 k) (h2 k)), max_self]

-- ============ 收缩系统（ContractingSystem）：动力学层的抽象骨架 ============

/-
  【收缩系统：自反收敛这一层的抽象】

  "智能 = 调节洞"的核心不是 s/r/n 的具体含义，而是**调节把偏差减半**这个机制。
  把它抽出来：

    ContractingSystem :=
      一个状态类型 + 一步算子 step + 偏差度量 dev，且 dev(step x) = dev(x)/2。

  通用事实（对任何收缩系统成立）：
    (1) 迭代公式：dev(step^k x) = dev(x) / 2^k
    (2) 严格收缩：dev x ≠ 0 ⟹ |dev(step^k x)| 严格递减
    (3) 构造性收敛：任意 ε > 0，存在 k 使 |dev(step^k x)| < ε
        —— 不用 ℝ 极限，用 ℚ 的 Archimedes 性（存在 n 使 q < n ≤ 2^n）。

  差异论的自反（reflectStep）只是它的一个实例：step = reflectStep，dev = deviation。
  这就是"动力学层"与"层/计数层"并列的第三个独立数学层。
-/

/-- 收缩系统：一步把偏差减半的动力学。 -/
structure ContractingSystem where
  state : Type*
  step : state → state
  dev : state → ℚ
  h_shrink : ∀ x, dev (step x) = dev x / 2

namespace ContractingSystem

-- 迭代 k 步。
def iter (S : ContractingSystem) : ℕ → S.state → S.state
  | 0, x => x
  | k + 1, x => S.step (S.iter k x)

-- (1) 迭代公式：偏差 = 初始偏差 / 2^k。
theorem dev_iter (S : ContractingSystem) (x : S.state) (k : ℕ) :
    S.dev (S.iter k x) = S.dev x / 2 ^ k := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
      change S.dev (S.step (S.iter k x)) = S.dev x / 2 ^ (k + 1)
      rw [S.h_shrink, ih, pow_succ]
      ring

-- (2) 严格收缩：非零偏差，一步后绝对值严格变小。
theorem dev_strict_shrink (S : ContractingSystem) (x : S.state) (h : S.dev x ≠ 0) :
    |S.dev (S.step x)| < |S.dev x| := by
  rw [S.h_shrink, abs_div]
  have hpos : 0 < |S.dev x| := abs_pos.mpr h
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  linarith

end ContractingSystem

-- 任意有理数都能被某个 2^k 超过（ℚ 的 Archimedes 性，构造性）。
-- 由 exists_nat_gt 与 n < 2^n 拼出。
theorem exists_two_pow_gt (q : ℚ) : ∃ k : ℕ, q < (2 : ℚ) ^ k := by
  obtain ⟨n, hn⟩ := exists_nat_gt q
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  have h : n ≤ 2 ^ n := le_of_lt (Nat.lt_two_pow_self)
  exact_mod_cast h

namespace ContractingSystem

-- (3) 构造性收敛：任意 ε > 0，存在 k 使 |偏差| < ε。
-- 不用 ℝ 极限：直接给出 k = ceil(|dev x| / ε) 的界（存在性由 Archimedes 保证）。
theorem dev_converges (S : ContractingSystem) (x : S.state) {ε : ℚ} (hε : 0 < ε) :
    ∃ k : ℕ, |S.dev (S.iter k x)| < ε := by
  obtain ⟨k, hk⟩ := exists_two_pow_gt (|S.dev x| / ε)
  refine ⟨k, ?_⟩
  rw [S.dev_iter, abs_div]
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  rw [abs_of_pos hpow]
  have h2 : |S.dev x| < (2 : ℚ) ^ k * ε := (div_lt_iff₀ hε).mp hk
  rw [div_lt_iff₀ hpow]
  linarith

end ContractingSystem

-- ============ 深水区 2：差异对象抽象（s/r/n 是内在度量，非 ℚ 占位） ============

/-
  【差异对象 = 主体（自指动作的载体），s/r/n 是它的内在度量】

  灵感："差异是意识主体的动作，ℚ 是发生的地方，有限性是唯一根"。
  所以差异不是散落的三个 ℚ（s r n），而是一个"对象"（主体 self），
  s（连通度=撑洞）、r（消解深度=钻洞）、n（层级=凝结点）是它的三个内在度量。

  雪球边界内建：0 ≤ s ≤ r、0 < r——之前是"外挂假设"，现在内建进对象。
  reflect 保持边界 ⟺ 层级 n ∈ [0,1]（由雪球比 s/r ∈ [0,1] 推出目标 n ∈ [0,1]）。
-/

structure DifferenceObject where
  s : ℚ   -- 连通度（撑洞）
  r : ℚ   -- 消解深度（钻洞）
  n : ℚ   -- 层级（凝结点）
  h_nonneg : 0 ≤ s
  h_sle_r : s ≤ r
  h_rpos : 0 < r
  h_nnonneg : 0 ≤ n
  h_nle_one : n ≤ 1

namespace DifferenceObject

-- 层级 n = 公共维度 / 总维度（凝结深度：两个状态共享的维度占比）。
def levelOf (m n : ℕ) : ℚ := (min m n : ℚ) / (max m n : ℚ)

-- 层级天然 ∈ [0,1]（公共维度 ≤ 总维度）。
theorem levelOf_mem_Icc (m n : ℕ) (hmn : 0 < max m n) : levelOf m n ∈ Set.Icc (0 : ℚ) 1 := by
  unfold levelOf
  have hmaxpos : 0 < (max m n : ℚ) := by exact_mod_cast hmn
  have hmin_nonneg : 0 ≤ (min m n : ℚ) := by exact_mod_cast (Nat.zero_le (min m n))
  have hmin_le_max : (min m n : ℚ) ≤ (max m n : ℚ) := by
    exact_mod_cast (le_trans (Nat.min_le_left m n) (Nat.le_max_left m n))
  constructor
  · exact div_nonneg hmin_nonneg (le_of_lt hmaxpos)
  · exact (div_le_one hmaxpos).mpr hmin_le_max

-- 从两个状态（的差异）度量出差异对象：s = s_rel（连通度），r = r_rel（深度），n = levelOf（层级）。
def ofStates {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (hm : 0 < m) (hn : 0 < n) : DifferenceObject :=
  { s := (s_rel x y : ℚ), r := (r_rel x y : ℚ), n := levelOf m n,
    h_nonneg := by exact_mod_cast (Nat.zero_le (s_rel x y)),
    h_sle_r := by exact_mod_cast (s_rel_le_r_rel x y),
    h_rpos := by
      unfold r_rel
      exact_mod_cast (Nat.lt_min.mpr ⟨hm, hn⟩),
    h_nnonneg := (levelOf_mem_Icc m n (Nat.lt_of_lt_of_le hn (Nat.le_max_right m n))).1,
    h_nle_one := (levelOf_mem_Icc m n (Nat.lt_of_lt_of_le hn (Nat.le_max_right m n))).2 }

-- 雪球比 s/r（落在 [0,1]，由约束保证）。
def ratio (d : DifferenceObject) : ℚ := d.s / d.r

-- 偏差 Δ = s/r − n。
def deviation (d : DifferenceObject) : ℚ := d.ratio - d.n

-- 稳定 ⟺ 偏差为零（⟺ s/r = n）。
theorem stable_iff_deviation_zero (d : DifferenceObject) :
    d.deviation = 0 ↔ d.ratio = d.n := by
  unfold deviation ratio
  constructor <;> intro h <;> linarith

-- 反射（自反算子）：把 s 拉到 n·r（目标），保持雪球边界（n ∈ [0,1] 内建）。
def reflect (d : DifferenceObject) : DifferenceObject :=
  { s := d.n * d.r, r := d.r, n := d.n,
    h_nonneg := mul_nonneg d.h_nnonneg (le_of_lt d.h_rpos),
    h_sle_r := by
      have hle : d.n * d.r ≤ 1 * d.r := mul_le_mul_of_nonneg_right d.h_nle_one (le_of_lt d.h_rpos)
      simpa using hle,
    h_rpos := d.h_rpos,
    h_nnonneg := d.h_nnonneg,
    h_nle_one := d.h_nle_one }

-- 反射后稳定：雪球比 = n。
theorem reflect_stable (d : DifferenceObject) :
    (reflect d).ratio = d.n := by
  unfold reflect ratio
  field_simp [d.h_rpos.ne']

-- 反射的不动点 ⟺ 稳定（可逆 = 不动点，差异对象版）。
theorem reflect_fixed_point_iff_stable (d : DifferenceObject) :
    reflect d = d ↔ d.ratio = d.n := by
  have hiff : reflect d = d ↔ d.n * d.r = d.s := by
    constructor
    · intro h
      simpa [reflect] using congrArg DifferenceObject.s h
    · intro hs
      rcases d with ⟨ds, dr, dn, h1, h2, h3, h4, h5⟩
      simp [reflect, hs]
  rw [hiff]
  unfold ratio
  constructor
  · intro h
    rw [← h]
    field_simp [d.h_rpos.ne']
  · intro h
    rw [← h]
    field_simp [d.h_rpos.ne']

-- 自我的驻留：reflect 的不动点 ⟺ 雪球平衡。
-- 与环上税台（对合型驻留）并列——这里是投影型驻留（reflect 幂等，非对合）。
theorem self_stasis_iff (d : DifferenceObject) :
    IsStasis reflect d ↔ d.ratio = d.n :=
  reflect_fixed_point_iff_stable d

-- 自反迭代（持续维持）：每次把 s 拉到稳定值 n·r 的一半（向不动点收敛）。
def reflectStep (d : DifferenceObject) : DifferenceObject :=
  { s := (d.s + d.n * d.r) / 2, r := d.r, n := d.n,
    h_nonneg := div_nonneg (add_nonneg d.h_nonneg (mul_nonneg d.h_nnonneg (le_of_lt d.h_rpos))) (by norm_num),
    h_sle_r := by
      have hnr_le : d.n * d.r ≤ d.r := by
        have : d.n * d.r ≤ 1 * d.r := mul_le_mul_of_nonneg_right d.h_nle_one (le_of_lt d.h_rpos)
        simpa using this
      nlinarith [d.h_sle_r, hnr_le],
    h_rpos := d.h_rpos,
    h_nnonneg := d.h_nnonneg,
    h_nle_one := d.h_nle_one }

-- 一次自反，偏差减半。
theorem reflectStep_deviation_half (d : DifferenceObject) :
    |(reflectStep d).deviation| = |d.deviation| / 2 := by
  unfold reflectStep deviation ratio
  have h : (d.s + d.n * d.r) / 2 / d.r - d.n = (d.s / d.r - d.n) / 2 := by
    field_simp [d.h_rpos.ne']
    ring
  rw [h]
  rw [abs_div]
  norm_num

-- 无绝对值版（收缩系统需要）：偏差恰好减半，符号不变。
theorem reflectStep_deviation (d : DifferenceObject) :
    (reflectStep d).deviation = d.deviation / 2 := by
  unfold reflectStep deviation ratio
  field_simp [d.h_rpos.ne']
  ring

-- 差异对象动力学 = 收缩系统（实例）：step = reflectStep，dev = deviation。
def reflectSystem : ContractingSystem where
  state := DifferenceObject
  step := reflectStep
  dev := DifferenceObject.deviation
  h_shrink := reflectStep_deviation

-- 覆盖：反射动力学的收敛定律就是收缩系统的通用定理。
-- (1) 迭代公式；(2) 严格收缩；(3) 构造性收敛（任意 ε > 0 有限步进入）。
theorem dynamical_layer_coverage :
    (∀ (S : ContractingSystem) (x : S.state) (k : ℕ),
        S.dev (S.iter k x) = S.dev x / 2 ^ k) ∧
    (∀ (S : ContractingSystem) (x : S.state), S.dev x ≠ 0 →
        |S.dev (S.step x)| < |S.dev x|) ∧
    (∀ (S : ContractingSystem) (x : S.state) {ε : ℚ}, 0 < ε →
        ∃ k : ℕ, |S.dev (S.iter k x)| < ε) ∧
    (∀ (d : DifferenceObject) (k : ℕ),
        (reflectSystem.iter k d).deviation = d.deviation / 2 ^ k) :=
  ⟨fun S x k => S.dev_iter x k,
   fun S x => S.dev_strict_shrink x,
   fun S x ε hε => S.dev_converges (ε := ε) x hε,
   fun d k => reflectSystem.dev_iter d k⟩

-- 调节方向（洞太大，Δ < 0）：reflectStep 单调增大 s，且不越过稳定值 n·r。
-- 洞太大（连通度不足）时，调节把 s 撑大、靠近稳定值，但绝不冲过头（不震荡）。
theorem reflectStep_mono_under {d : DifferenceObject} (h : d.s < d.n * d.r) :
    d.s < (reflectStep d).s ∧ (reflectStep d).s < d.n * d.r := by
  unfold reflectStep
  constructor <;> nlinarith [h]

-- 调节方向（洞太小，Δ > 0）：reflectStep 单调减小 s，且不越过稳定值 n·r。
-- 洞太小（连通度过剩）时，调节把 s 收缩、靠近稳定值，但绝不缩过头（不震荡）。
theorem reflectStep_mono_over {d : DifferenceObject} (h : d.n * d.r < d.s) :
    d.n * d.r < (reflectStep d).s ∧ (reflectStep d).s < d.s := by
  unfold reflectStep
  constructor <;> nlinarith [h]

-- 单调收敛：reflectStep 严格缩小 |偏差|（幅度减半，符号不变）。
-- 智能调节 = 有方向的收敛：每一步都朝稳定值走（mono_under/over），且 |偏差| 严格递减——
-- 单主体（自我）在不动点处停住损耗（对抗熵增），这就是"可逆 = 有不动点 = 停熵"的机制。
theorem reflectStep_strictly_converges {d : DifferenceObject} (hne : d.deviation ≠ 0) :
    |(reflectStep d).deviation| < |d.deviation| := by
  rw [reflectStep_deviation_half d]
  have hpos : 0 < |d.deviation| := abs_pos.mpr hne
  nlinarith

-- 自反迭代 k 次。
def reflectIter (d : DifferenceObject) (k : ℕ) : DifferenceObject :=
  Nat.rec d (fun _ prev => reflectStep prev) k

-- 迭代 k 次后偏差 = 初始偏差 / 2^k（构造性收敛到不动点）。
theorem reflectIter_deviation (d : DifferenceObject) (k : ℕ) :
    |(reflectIter d k).deviation| = |d.deviation| / (2 : ℚ) ^ k := by
  induction k with
  | zero => simp [reflectIter]
  | succ k ih =>
      change |(reflectStep (reflectIter d k)).deviation| = |d.deviation| / (2 : ℚ) ^ (k + 1)
      rw [reflectStep_deviation_half (reflectIter d k)]
      rw [ih]
      field_simp [pow_succ]
      ring

-- 自反 k 次（无绝对值版）：偏差恰好 = 初始偏差 / 2^k。
theorem reflectIter_deviation' (d : DifferenceObject) (k : ℕ) :
    (reflectIter d k).deviation = d.deviation / 2 ^ k := by
  induction k with
  | zero => simp [reflectIter]
  | succ k ih =>
      change (reflectStep (reflectIter d k)).deviation = d.deviation / 2 ^ (k + 1)
      rw [reflectStep_deviation, ih, pow_succ, div_div]

-- 【负指数 = 消解深度】自反 k 次，偏差乘以 2^(−k)。
-- 这就是"半值 = 2 的 −1 次幂"在动力学上的落地：
-- 每自反一次就把偏差乘一次 2^(−1) —— 半值不是中点，是"退一层分辨率"的算子。
theorem reflectIter_deviation_zpow (d : DifferenceObject) (k : ℕ) :
    (reflectIter d k).deviation = d.deviation * (2 : ℚ) ^ (-(k : ℤ)) := by
  rw [reflectIter_deviation', div_eq_mul_inv, zpow_neg, zpow_natCast]

end DifferenceObject

-- ============ 深水区 3：域、量对与有限管理 ============

/-
  【域 = 可管理的作用范围（不是陪域）】

  陪域是值的静态容器（f : X → Y，Y 是陪域，回答"值落在哪"）；
  归隐的"域"是**可管理的作用范围**——有限载体 + 读数 + 可调参数，
  回答的是"能管多大"。

  s 是连通度域（生界作用面），r 是深度域（公共作用面）。
  二者不独立：由**量对**（同一守恒量的几个读数）连接——

      s（生界读数：差异 > δ）+ j（暹界读数：= δ）+ d（死界读数：< δ）= r。

  这正是 D7 差异守恒在对象层面的离散形式：转移不消失，只在三域间重新分配。

  n 是智能：不是第三个读数，是**管理者**。它决定守恒量在三域间怎么分配，
  稳定性 s/r = n 就是"管理者把生界占比调节到 n"。

  【有限性为什么是控制的定义性前提】

    · 可枚举 ⇒ 最优配置存在且可在有限步内取到（有限最优，构造性，
      无需 ℝ 完备性、无需极限、无需经验积累）；
    · 可比较 ⇒ 稳定可判定（s/r = n 是 ℚ 上的等式判定）；
    · 可选择 ⇒ 管理 = 有限集上的选择（finite_choice_free），不需要无穷选择。

  所以控制 = 有限域上的可枚举调节。这也是天才"没学过、一上手就会"的形式：
  最优解在有限配置空间里**直接取到**，不需要通过经验迭代逼近；
  而且最优解只依赖守恒量与目标 n（闭式、内容无关）——所以同一套管理法则
  跨域通用，这正是通才的数学形态。

  意识则是"域管理自身"：有限主体管理自己的 s 域和 r 域，管理动作本身又在域中，
  自指必然留下够不着的位置——洞。无限没有"够不着"的地方，所以意识是有限性独有的。
-/

-- 公共域上的一维差异（第 i 个共同维度的差）。
def pairDiff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (i : Fin (min m n)) : ℚ :=
  x.val (Fin.embedLeft i) - y.val (Fin.embedRight i)

-- 生界读数载体：差异超过阈值 δ 的共同维度。
def aliveSet {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    Finset (Fin (min m n)) :=
  Finset.univ.filter (fun i => δ < |pairDiff x y i|)

-- 暹界读数载体：差异恰等于阈值 δ 的共同维度（临界格）。
def xianSet {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    Finset (Fin (min m n)) :=
  Finset.univ.filter (fun i => |pairDiff x y i| = δ)

-- 死界读数载体：差异低于阈值 δ 的共同维度（盲区）。
def deadSet {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    Finset (Fin (min m n)) :=
  Finset.univ.filter (fun i => |pairDiff x y i| < δ)

-- 三个读数：域上的有限计数。
def sReading {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : ℕ :=
  (aliveSet x y δ).card
def xianReading {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : ℕ :=
  (xianSet x y δ).card
def dReading {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : ℕ :=
  (deadSet x y δ).card

-- 构造性三分解基数守恒（不用 Classical 的 filter 补集引理）：
-- 有限集按"小于 / 等于 / 大于阈值"三分，三部分基数之和 = 全集基数。
theorem card_split3 {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℚ) (δ : ℚ) :
    (s.filter (fun a => δ < |f a|)).card + (s.filter (fun a => |f a| = δ)).card +
      (s.filter (fun a => |f a| < δ)).card = s.card := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha]
      rcases lt_trichotomy (|f a|) δ with hlt | heq | hgt
      · -- |f a| < δ：新元素落入死界
        have h1 : ¬ δ < |f a| := not_lt.mpr (le_of_lt hlt)
        have h2 : ¬ |f a| = δ := ne_of_lt hlt
        rw [Finset.filter_insert, ite_eq_right h1, Finset.filter_insert, ite_eq_right h2,
          Finset.filter_insert, ite_eq_left hlt,
          Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
        omega
      · -- |f a| = δ：新元素落入暹界
        have h1 : ¬ δ < |f a| := not_lt.mpr (le_of_eq heq)
        have h3 : ¬ |f a| < δ := not_lt.mpr (le_of_eq heq.symm)
        rw [Finset.filter_insert, ite_eq_right h1, Finset.filter_insert, ite_eq_left heq,
          Finset.filter_insert, ite_eq_right h3,
          Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
        omega
      · -- δ < |f a|：新元素落入生界
        have h2 : ¬ |f a| = δ := ne_of_gt hgt
        have h3 : ¬ |f a| < δ := not_lt.mpr (le_of_lt hgt)
        rw [Finset.filter_insert, ite_eq_left hgt, Finset.filter_insert, ite_eq_right h2,
          Finset.filter_insert, ite_eq_right h3,
          Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
        omega

-- 【量对守恒】生 + 暹 + 死 = 公共域（同一守恒量的三个读数）。
theorem qty_pair_conservation {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    sReading x y δ + xianReading x y δ + dReading x y δ = r_rel x y := by
  unfold sReading xianReading dReading aliveSet xianSet deadSet r_rel
  have h := card_split3 (Finset.univ : Finset (Fin (min m n)))
    (fun i => pairDiff x y i) δ
  simpa using h

-- 生界读数不超过公共域。
theorem sReading_le_r_rel {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    sReading x y δ ≤ r_rel x y := by
  unfold sReading r_rel
  simpa [aliveSet] using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin (min m n))))
    (p := fun i => δ < |pairDiff x y i|))

-- 死界读数不超过公共域。
theorem dReading_le_r_rel {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    dReading x y δ ≤ r_rel x y := by
  unfold dReading r_rel
  simpa [deadSet] using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin (min m n))))
    (p := fun i => |pairDiff x y i| < δ))

-- δ = 0：死界为空（没有维度能"低于 0"）。
theorem dReading_zero {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : dReading x y 0 = 0 := by
  unfold dReading deadSet
  rw [Finset.filter_false_of_mem (fun i _ => not_lt.mpr (abs_nonneg _))]
  rfl

-- δ = 0：生界读数退化为 s_rel（"不同"就是"差异 > 0"）。
theorem sReading_zero_eq_s_rel {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    sReading x y 0 = s_rel x y := by
  unfold sReading aliveSet s_rel
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show (0 : ℚ) < |pairDiff x y i| ↔ x.val (Fin.embedLeft i) ≠ y.val (Fin.embedRight i)
  unfold pairDiff
  rw [abs_pos, sub_ne_zero]

-- δ = 0：守恒退化为"生 + 暹 = 公共域"（死界清空）。
theorem qty_pair_zero {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    sReading x y 0 + xianReading x y 0 = r_rel x y := by
  have h := qty_pair_conservation x y 0
  rw [dReading_zero] at h
  omega

-- 【稳定 = 分配落格】管理偏差为零 ⟺ 生界读数恰为 n·r（智能的分配恰好落在格点上）。
theorem manage_stable_iff (r s : ℕ) (n : ℚ) (hr : 0 < r) :
    |(s : ℚ) / r - n| = 0 ↔ (s : ℚ) = n * r := by
  rw [abs_eq_zero, sub_eq_zero]
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  constructor
  · intro h
    rwa [div_eq_iff hrq] at h
  · intro h
    rw [h]
    field_simp

-- 量对：两个域 + 守恒（生 + 暹 + 死 = 公共域）。
structure QtyPair where
  s : ℕ   -- 生界读数（域 S）
  j : ℕ   -- 暹界读数（临界格）
  d : ℕ   -- 死界读数（域 D）
  r : ℕ   -- 公共域（守恒总量）
  h_conservation : s + j + d = r

-- 由差异读数直接构造量对（全部内在生成，无 ℚ 占位假设）。
def QtyPair.ofStates {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : QtyPair where
  s := sReading x y δ
  j := xianReading x y δ
  d := dReading x y δ
  r := r_rel x y
  h_conservation := qty_pair_conservation x y δ

namespace QtyPair

-- 守恒推出 s ≤ r（生界不超过公共域）。
theorem s_le_r (q : QtyPair) : q.s ≤ q.r := by
  have := q.h_conservation; omega

-- 守恒推出 d ≤ r。
theorem d_le_r (q : QtyPair) : q.d ≤ q.r := by
  have := q.h_conservation; omega

-- 管理目标：生界读数占公共域的比例（智能 n 要调节的量）。
def ratio (q : QtyPair) : ℚ := (q.s : ℚ) / (q.r : ℚ)

-- 管理偏差：|比例 − n|。
def deviation (q : QtyPair) (n : ℚ) : ℚ := |q.ratio - n|

-- 量对 + 智能 n = 差异对象（雪球条件的载体）：所有字段内在生成。
def toDifferenceObject (q : QtyPair) (n : ℚ) (hn0 : 0 ≤ n) (hn1 : n ≤ 1) (hr : 0 < q.r) :
    DifferenceObject where
  s := (q.s : ℚ)
  r := (q.r : ℚ)
  n := n
  h_nonneg := Nat.cast_nonneg q.s
  h_sle_r := by exact_mod_cast q.s_le_r
  h_rpos := by exact_mod_cast hr
  h_nnonneg := hn0
  h_nle_one := hn1

-- 雪球稳定 ⟺ 智能的分配恰好落格（生界读数 = n·公共域）。
theorem toDifferenceObject_stable_iff (q : QtyPair) (n : ℚ) (hn0 : 0 ≤ n) (hn1 : n ≤ 1)
    (hr : 0 < q.r) :
    (q.toDifferenceObject n hn0 hn1 hr).deviation = 0 ↔ (q.s : ℚ) = n * q.r := by
  unfold DifferenceObject.deviation DifferenceObject.ratio
  simp only [toDifferenceObject]
  rw [← abs_eq_zero]
  exact manage_stable_iff q.r q.s n hr

end QtyPair

-- 【有限最优】有限非空类型上的 ℚ 值函数取到最小值（构造性，无 ℝ 完备性）。
theorem finite_optimum {α : Type*} [Fintype α] [Nonempty α] (f : α → ℚ) :
    ∃ x, ∀ y, f x ≤ f y := by
  obtain ⟨x, -, hx⟩ := Finset.exists_min_image (Finset.univ : Finset α) f Finset.univ_nonempty
  exact ⟨x, fun y => hx y (Finset.mem_univ y)⟩

-- 管理者的可选配置：生界读数 s ∈ {0,1,…,r}（有限的格点集合）。
def manageConfigs (r : ℕ) : Finset ℕ := Finset.range (r + 1)

-- 【有限最优管理】存在最优格点使 |s/r − n| 达到最小（构造性）。
-- 这就是"控制建立在有限基础上"的精确形式：
-- 管理不需要经验积累、不需要极限，最优配置在有限集里直接取到。
theorem manage_optimum (r : ℕ) (n : ℚ) (_hr : 0 < r) :
    ∃ s ∈ manageConfigs r, ∀ s' ∈ manageConfigs r,
      |(s : ℚ) / r - n| ≤ |(s' : ℚ) / r - n| := by
  have hne : (manageConfigs r).Nonempty := ⟨0, by simp [manageConfigs]⟩
  exact Finset.exists_min_image (manageConfigs r) (fun s => |(s : ℚ) / r - n|) hne

-- 【夹格】整数最优解必然夹住目标：|k − x| < 1，否则相邻整数更近。
-- 这就是"最优解 = 夹住转轴的那一格"（与半转合图的夹格是同一件事）。
theorem int_optimum_bracket (x : ℚ) (k : ℤ)
    (hmin : ∀ k' : ℤ, |((k : ℚ)) - x| ≤ |((k' : ℚ)) - x|) :
    |((k : ℚ)) - x| < 1 := by
  by_contra h
  push Not at h
  rcases le_abs.mp h with h1 | h1
  · -- 1 ≤ (k:ℚ) − x：k−1 更近
    have hk : ((k - 1 : ℤ) : ℚ) - x = (((k : ℚ) - x) - 1) := by push_cast; ring
    have hlt : |((k - 1 : ℤ) : ℚ) - x| < |((k : ℚ)) - x| := by
      rw [hk]
      have habs : |((k : ℚ) - x) - 1| = ((k : ℚ) - x) - 1 := by
        rw [abs_of_nonneg]
        linarith
      have hkabs : |((k : ℚ) - x)| = ((k : ℚ) - x) := abs_of_pos (by linarith)
      rw [habs, hkabs]
      linarith
    have := hmin (k - 1)
    linarith
  · -- 1 ≤ -((k:ℚ) − x)：k+1 更近
    have hk : ((k + 1 : ℤ) : ℚ) - x = (((k : ℚ) - x) + 1) := by push_cast; ring
    have hkx : ((k : ℚ) - x) ≤ 0 := by linarith
    have hlt : |((k + 1 : ℤ) : ℚ) - x| < |((k : ℚ)) - x| := by
      rw [hk, abs_of_nonpos (by linarith), abs_of_nonpos hkx]
      linarith
    have := hmin (k + 1)
    linarith

-- 目标不在整格上 ⟹ 任何读数都不可能稳定（偏差恒正）。
theorem stable_unreachable_of_not_int {r s : ℕ} {n : ℚ} (hr : 0 < r)
    (h : ¬ ∃ k : ℤ, (k : ℚ) = n * r) :
    |(s : ℚ) / r - n| ≠ 0 := by
  intro hzero
  have hs : (s : ℚ) = n * r := (manage_stable_iff r s n hr).mp hzero
  exact h ⟨(s : ℤ), by simpa using hs⟩

-- 迭代（经验）永远到不了最优格：偏差非零 ⇒ 任何有限步后仍非零。
theorem reflectIter_never_stable {d : DifferenceObject} (h : d.deviation ≠ 0) (k : ℕ) :
    (DifferenceObject.reflectIter d k).deviation ≠ 0 := by
  rw [DifferenceObject.reflectIter_deviation']
  exact div_ne_zero h (pow_ne_zero _ (by norm_num))

-- 【智能的形态】有限性下的最优解：
--   · 最优配置存在且可取（manage_optimum）；
--   · 最优格点必然夹住目标：|s* − n·r| < 1（int_optimum_bracket）；
--   · 迭代（经验）在有限步内永远到不了零偏差（reflectIter_never_stable）；
--   · 目标不在整格时稳定根本不存在，最优也只能是"最近的两格"（stable_unreachable_of_not_int）。
-- 所以：天才不是学得快，而是**在有限配置空间里直接取到最优**——
-- 最优解只依赖守恒量和目标 n，不依赖域的内容，故同一法则跨域通用（通才）。
theorem finite_intelligence :
    (∀ (r : ℕ) (n : ℚ), 0 < r → ∃ s ∈ manageConfigs r,
      ∀ s' ∈ manageConfigs r, |(s : ℚ) / r - n| ≤ |(s' : ℚ) / r - n|) ∧
    (∀ (x : ℚ) (k : ℤ),
      (∀ k' : ℤ, |((k : ℚ)) - x| ≤ |((k' : ℚ)) - x|) → |((k : ℚ)) - x| < 1) ∧
    (∀ (d : DifferenceObject), d.deviation ≠ 0 → ∀ k : ℕ,
      (DifferenceObject.reflectIter d k).deviation ≠ 0) ∧
    (∀ (r s : ℕ) (n : ℚ), 0 < r → (¬ ∃ k : ℤ, (k : ℚ) = n * r) →
      |(s : ℚ) / r - n| ≠ 0) :=
  ⟨manage_optimum, int_optimum_bracket,
   fun _d h k => reflectIter_never_stable h k,
   fun _r _s _n hr h => stable_unreachable_of_not_int hr h⟩

-- ============ 深水区 4：智能选阈值（δ 管理） ============

/-
  【管理 = 在有限的阈值候选里选 δ】

  s、j、d 都是 δ 的函数：δ 升高（分辨率变粗），维度从生界退入死界。
  但 δ 不必在 ℚ 里任意取：读数只取决于 δ 跨越了哪些差异值。
  所以真正的候选阈值只有有限个：

      manageThresholds = {−1, 0} ∪ {|d_i|}（所有共同维度的差异绝对值）。

  两个定理：
    · 阈值归约：任何 δ 的读数，都能在有限候选里找到等价的 δ'；
    · 阈值最优：在有限候选里直接取到使 |s(δ)/r − n| 最小的 δ。
  ——这就是"智能 = 有限域上的最优选择"在 δ 方向上的落地。
-/

-- 有限的候选阈值集合：{−1, 0} ∪ 所有差异绝对值。
def manageThresholds {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : Finset ℚ :=
  insert (-1) (insert 0 (Finset.univ.image (fun i : Fin (min m n) => |pairDiff x y i|)))

-- 生界读数对 δ 反单调：δ 越大（层越粗），生界越少。
theorem sReading_antitone {m n : ℕ} (x : StateQuant m) (y : StateQuant n) {δ₁ δ₂ : ℚ}
    (h : δ₁ ≤ δ₂) : sReading x y δ₂ ≤ sReading x y δ₁ := by
  unfold sReading aliveSet
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_le_of_lt h hi.2⟩

-- δ = −1（低于一切差异值）：所有维度都在生界，读数 = 公共域。
theorem sReading_neg_one {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    sReading x y (-1) = r_rel x y := by
  unfold sReading aliveSet r_rel
  rw [Finset.filter_true_of_mem (fun i _ => by linarith [abs_nonneg (pairDiff x y i)])]
  simp

-- 【阈值归约】任何 δ 的读数，都可由有限候选集合中的某个 δ' 实现。
theorem threshold_reduction {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    ∃ δ' ∈ manageThresholds x y, sReading x y δ' = sReading x y δ := by
  by_cases h : ∃ c ∈ manageThresholds x y, c ≤ δ
  · obtain ⟨c, hc, hcle⟩ := h
    let S := (manageThresholds x y).filter (fun t => t ≤ δ)
    have hSne : S.Nonempty := ⟨c, Finset.mem_filter.mpr ⟨hc, hcle⟩⟩
    have hmem := Finset.max'_mem S hSne
    refine ⟨S.max' hSne, (Finset.mem_filter.mp hmem).1, ?_⟩
    have hle : S.max' hSne ≤ δ := (Finset.mem_filter.mp hmem).2
    unfold sReading aliveSet
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_contra hδv
      push Not at hδv
      have hvS : |pairDiff x y i| ∈ S := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))), hδv⟩
      have hle' : |pairDiff x y i| ≤ S.max' hSne := Finset.le_max' S _ hvS
      linarith
    · intro hi
      exact lt_of_le_of_lt hle hi
  · push Not at h
    have hneg : δ < (-1 : ℚ) := h (-1) (by simp [manageThresholds])
    refine ⟨-1, by simp [manageThresholds], ?_⟩
    unfold sReading aliveSet
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      linarith [abs_nonneg (pairDiff x y i)]
    · intro _
      linarith [abs_nonneg (pairDiff x y i)]

-- 【阈值最优】在有限候选阈值里直接取到最优 δ（构造性）。
theorem manage_threshold_optimum {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (target : ℚ) :
    ∃ δ' ∈ manageThresholds x y, ∀ δ ∈ manageThresholds x y,
      |(sReading x y δ' : ℚ) / r_rel x y - target|
        ≤ |(sReading x y δ : ℚ) / r_rel x y - target| := by
  have hne : (manageThresholds x y).Nonempty := ⟨-1, by simp [manageThresholds]⟩
  exact Finset.exists_min_image _
    (fun δ => |(sReading x y δ : ℚ) / r_rel x y - target|) hne

-- 【δ 方向的智能】反单调 + 有限候选归约 + 有限最优 + 下端点全生。
theorem finite_management_by_threshold :
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ →
      sReading x y δ₂ ≤ sReading x y δ₁) ∧
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ),
      ∃ δ' ∈ manageThresholds x y, sReading x y δ' = sReading x y δ) ∧
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (target : ℚ),
      ∃ δ' ∈ manageThresholds x y, ∀ δ ∈ manageThresholds x y,
        |(sReading x y δ' : ℚ) / r_rel x y - target|
          ≤ |(sReading x y δ : ℚ) / r_rel x y - target|) ∧
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n), sReading x y (-1) = r_rel x y) :=
  ⟨fun x y => sReading_antitone x y,
   fun x y δ => threshold_reduction x y δ,
   fun x y target => manage_threshold_optimum x y target,
   fun x y => sReading_neg_one x y⟩

-- ============ 深水区 5：δ 方向的凝结 / 消解（层间转移的精确计数） ============

/-
  【δ 方向的凝结与消解：不是维度投影，是层间翻越】

  coarsen/condense 是**维度转移**（投影/补 0）。这里做 **δ 方向的转移**：
  阈值一移动，维度就在死界/暹界/生界之间翻越。

  设 δ₁ ≤ δ₂（δ₁ 更细，δ₂ 更粗）：

    · δ-消解（粗化，δ₁→δ₂）：transferDown = #{δ₁ ≤ |d_i| < δ₂}
      有多少维度从生界/暹界退入死界；
    · δ-凝结（细化，δ₂→δ₁）：transferUp = #{δ₁ < |d_i| ≤ δ₂}
      有多少维度从死界翻入生界。

  三条精确律：
    (1) 生界账面：s(δ₁) = s(δ₂) + transferUp；
    (2) 死界账面：d(δ₂) = d(δ₁) + transferDown；
    (3) 层间守恒：transferUp + j(δ₁) = transferDown + j(δ₂)
        ——转移计数与暹界读数之差在两层的账本上完全对得上（量对的层间版）。

  以及暹界的有限支撑：j(δ) > 0 ⟺ δ 恰好等于某个 |d_i|。
  所以层的全部"事件"只发生在有限的格点上，与 manageThresholds 一致。
-/

-- δ-凝结转移计数：从粗层 δ₂ 降到细层 δ₁ 时，死界翻入生界的维数。
def transferUp {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ₁ δ₂ : ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (min m n) =>
    δ₁ < |pairDiff x y i| ∧ |pairDiff x y i| ≤ δ₂)).card

-- δ-消解转移计数：从细层 δ₁ 抬到粗层 δ₂ 时，生界/暹界退入死界的维数。
def transferDown {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ₁ δ₂ : ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (min m n) =>
    δ₁ ≤ |pairDiff x y i| ∧ |pairDiff x y i| < δ₂)).card

-- (1) 生界账面：细化后新增的生界读数 = 翻越的维数。
theorem sReading_transfer {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    sReading x y δ₁ = sReading x y δ₂ + transferUp x y δ₁ δ₂ := by
  unfold sReading aliveSet transferUp
  have hunion : (Finset.univ.filter (fun i : Fin (min m n) => δ₂ < |pairDiff x y i|))
      ∪ (Finset.univ.filter (fun i : Fin (min m n) =>
          δ₁ < |pairDiff x y i| ∧ |pairDiff x y i| ≤ δ₂))
      = (Finset.univ.filter (fun i : Fin (min m n) => δ₁ < |pairDiff x y i|)) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h1 | ⟨h1, _⟩) <;> linarith
    · intro h1
      by_cases h2 : δ₂ < |pairDiff x y i|
      · exact Or.inl h2
      · push Not at h2
        exact Or.inr ⟨h1, h2⟩
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (min m n) => δ₂ < |pairDiff x y i|))
      (Finset.univ.filter (fun i : Fin (min m n) =>
        δ₁ < |pairDiff x y i| ∧ |pairDiff x y i| ≤ δ₂)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    linarith [hi, hj.2]
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

-- (2) 死界账面：粗化后新增的死界读数 = 退入的维数。
theorem dReading_transfer {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    dReading x y δ₂ = dReading x y δ₁ + transferDown x y δ₁ δ₂ := by
  unfold dReading deadSet transferDown
  have hunion : (Finset.univ.filter (fun i : Fin (min m n) => |pairDiff x y i| < δ₁))
      ∪ (Finset.univ.filter (fun i : Fin (min m n) =>
          δ₁ ≤ |pairDiff x y i| ∧ |pairDiff x y i| < δ₂))
      = (Finset.univ.filter (fun i : Fin (min m n) => |pairDiff x y i| < δ₂)) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h1 | ⟨_, h2⟩) <;> linarith
    · intro h2
      by_cases h1 : |pairDiff x y i| < δ₁
      · exact Or.inl h1
      · push Not at h1
        exact Or.inr ⟨h1, h2⟩
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (min m n) => |pairDiff x y i| < δ₁))
      (Finset.univ.filter (fun i : Fin (min m n) =>
        δ₁ ≤ |pairDiff x y i| ∧ |pairDiff x y i| < δ₂)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    linarith [hi, hj.1]
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

-- (3) 层间守恒：转移计数 + 暹界读数，在两层的账本上对得上（量对的层间版）。
theorem transfer_conservation {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    transferUp x y δ₁ δ₂ + xianReading x y δ₁
      = transferDown x y δ₁ δ₂ + xianReading x y δ₂ := by
  have hs := sReading_transfer x y h
  have hd := dReading_transfer x y h
  have hc₁ := qty_pair_conservation x y δ₁
  have hc₂ := qty_pair_conservation x y δ₂
  omega

-- 暹界只在有限格点上出现：j(δ) > 0 ⟺ δ 恰等于某个差异绝对值。
theorem xianReading_pos_iff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    0 < xianReading x y δ ↔ ∃ i : Fin (min m n), |pairDiff x y i| = δ := by
  unfold xianReading xianSet
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp

-- 暹界的支撑落在有限候选集合里（与 manageThresholds 一致）。
theorem xian_support_finite {m n : ℕ} (x : StateQuant m) (y : StateQuant n) {δ : ℚ}
    (h : 0 < xianReading x y δ) :
    δ ∈ Finset.univ.image (fun i : Fin (min m n) => |pairDiff x y i|) := by
  rw [xianReading_pos_iff] at h
  obtain ⟨i, hi⟩ := h
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

-- 【δ 方向的凝结/消解】三层账本 + 层间守恒 + 暹界有限支撑。
theorem layer_transfer_law :
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ →
      sReading x y δ₁ = sReading x y δ₂ + transferUp x y δ₁ δ₂) ∧
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ →
      dReading x y δ₂ = dReading x y δ₁ + transferDown x y δ₁ δ₂) ∧
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ →
      transferUp x y δ₁ δ₂ + xianReading x y δ₁
        = transferDown x y δ₁ δ₂ + xianReading x y δ₂) ∧
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ),
      0 < xianReading x y δ ↔ ∃ i : Fin (min m n), |pairDiff x y i| = δ) :=
  ⟨fun x y => sReading_transfer x y,
   fun x y => dReading_transfer x y,
   fun x y => transfer_conservation x y,
   fun x y δ => xianReading_pos_iff x y δ⟩

-- ============ D1 差异网络：节点不是先验的点，是差异对的凝结残影 ============

/-
  【D1：差异网络 𝒩】

  原文：差异网络的基本单元是差异对 (x, y)；当两对差异 (x,y) 与 (x',y') 的
  强度在当前层不可区分时，它们凝结为同一节点。"没有先验的点。点是差异关系
  被感知后的凝结残影。"

  形式化：
    · 网络 = κ 个差异对的有限族（left i, right i）；
    · 强度 strength i = commonDist (left i) (right i)；
    · 层 δ 的不可区分 = |strength i − strength j| ≤ δ；
    · 节点空间 = 该关系的传递闭包之商（凝结残影），节点数 = 层读数。

  四条网络定律：
    (1) 投影满射：每个节点都是某些差异对的残影（点不是先验的）；
    (2) 节点数反单调：δ 越大（层越粗），节点越少（凝结单调）；
    (3) δ = 0：节点 = 强度完全相同的差异对（残影退化为强度层）；
    (4) 网络量对守恒（D7 有限簇版）：网络的生 + 暹 + 死总读数 = 网络总量。
-/

-- 关系"值相等"的传递闭包就是值相等（构造性）。
theorem reflTransGen_eq_iff {α : Type*} {β : Type*} (f : α → β) (i j : α) :
    Relation.ReflTransGen (fun a b => f a = f b) i j ↔ f i = f j := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans hbc
  · intro h
    exact Relation.ReflTransGen.single h

-- 有限差异网络：κ 个差异对（每个由两个同维状态构成）。
structure DiffNet (κ n : ℕ) where
  left : Fin κ → StateQuant n
  right : Fin κ → StateQuant n

namespace DiffNet

variable {κ n : ℕ} (N : DiffNet κ n)

-- 差异强度：一个差异对的 D 值。
def strength (i : Fin κ) : ℚ := commonDist (N.left i) (N.right i)

-- 层 δ 下的"强度不可区分"：两对差异的强度相差不超过 δ。
def step (δ : ℚ) (i j : Fin κ) : Prop := |N.strength i - N.strength j| ≤ δ

-- 不可区分关系对称（|a−b| = |b−a|）。
theorem step_symm (δ : ℚ) {i j : Fin κ} (h : N.step δ i j) : N.step δ j i := by
  unfold step at h ⊢
  rwa [abs_sub_comm]

-- 节点 = 差异对按强度不可区分的凝结类（D1 的"残影"）。
def nodeSetoid (δ : ℚ) : Setoid (Fin κ) :=
  closureSetoid (N.step δ) (fun _ _ h => N.step_symm δ h)

-- 层 δ 下的节点空间（凝结商）。
abbrev Node (δ : ℚ) : Type := Quotient (N.nodeSetoid δ)

-- 凝结投影：每个差异对落入一个节点。
def nodeOf (δ : ℚ) (i : Fin κ) : N.Node δ := Quotient.mk (N.nodeSetoid δ) i

-- 强度不可区分的可判定性。
@[instance_reducible]
def stepDecidable (δ : ℚ) : DecidableRel (N.step δ) :=
  fun i j => by unfold step; infer_instance

-- 节点关系的可判定性（构造性：有限类型上的传递闭包可判定）。
@[instance_reducible]
def nodeDecidable (δ : ℚ) : DecidableRel (N.nodeSetoid δ).r :=
  fun a b =>
    letI := N.stepDecidable δ
    reflTransGen_decidable (r := N.step δ) a b

-- 节点数（层读数）。
def nodeCount (δ : ℚ) : ℕ :=
  letI := N.nodeDecidable δ
  Fintype.card (Quotient (N.nodeSetoid δ))

-- (1) 投影满射：每个节点都是某些差异对的残影——点不是先验的。
theorem nodeOf_surjective (δ : ℚ) : Function.Surjective (N.nodeOf δ) := by
  intro q
  induction q using Quotient.ind with
  | _ i => exact ⟨i, rfl⟩

-- (2) 节点数反单调：δ 越大（层越粗），节点越少（凝结单调）。
set_option linter.style.haveILetI false in
theorem nodeCount_antitone {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    N.nodeCount δ₂ ≤ N.nodeCount δ₁ := by
  unfold nodeCount
  letI := N.nodeDecidable δ₁
  letI := N.nodeDecidable δ₂
  have hsub : ∀ a b, N.step δ₁ a b → N.step δ₂ a b := by
    intro a b hab
    unfold step at hab ⊢
    linarith
  let f : Quotient (N.nodeSetoid δ₁) → Quotient (N.nodeSetoid δ₂) :=
    Quotient.map id (fun a b hab => reflTransGen_mono hsub a b hab)
  have hsurj : Function.Surjective f :=
    Quotient.map_surjective (fun a b hab => reflTransGen_mono hsub a b hab)
      (fun y => ⟨y, rfl⟩)
  exact Fintype.card_le_of_surjective f hsurj

-- 层 0 的不可区分 = 强度相等。
theorem step_zero_iff (i j : Fin κ) : N.step 0 i j ↔ N.strength i = N.strength j := by
  unfold step
  constructor
  · intro h
    have h0 : |N.strength i - N.strength j| = 0 := le_antisymm h (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h0)
  · intro h
    rw [h, sub_self, abs_zero]

-- (3) δ = 0：节点 = 强度完全相同的差异对（残影退化为强度层）。
theorem node_zero_iff (i j : Fin κ) :
    (N.nodeSetoid 0).r i j ↔ N.strength i = N.strength j := by
  change Relation.ReflTransGen (N.step 0) i j ↔ N.strength i = N.strength j
  rw [reflTransGen_congr (fun a b => N.step_zero_iff a b)]
  exact reflTransGen_eq_iff N.strength i j

-- 不同强度在 δ = 0 必是不同节点（节点 = 残影，残影由强度决定）。
theorem node_ne_zero_of_strength_ne {i j : Fin κ} (h : N.strength i ≠ N.strength j) :
    N.nodeOf 0 i ≠ N.nodeOf 0 j := by
  intro heq
  exact h ((N.node_zero_iff i j).mp (Quotient.exact heq))

-- 网络的边读数：每个差异对携带一个量对（生/暹/死三读 + 公共域）。
def edgeQty (δ : ℚ) (i : Fin κ) : QtyPair :=
  QtyPair.ofStates (N.left i) (N.right i) δ

-- 网络总量读：生 / 暹 / 死 / 公共域。
def totalAlive (δ : ℚ) : ℕ := ∑ i : Fin κ, (N.edgeQty δ i).s
def totalXian (δ : ℚ) : ℕ := ∑ i : Fin κ, (N.edgeQty δ i).j
def totalDead (δ : ℚ) : ℕ := ∑ i : Fin κ, (N.edgeQty δ i).d
def totalR (δ : ℚ) : ℕ := ∑ i : Fin κ, (N.edgeQty δ i).r

-- (4) 网络量对守恒（D7 的有限簇版）：
-- 整个网络的生 + 暹 + 死总读数 = 网络总量。三域只是重新分配，总量守恒。
theorem net_qty_pair_conservation (δ : ℚ) :
    N.totalAlive δ + N.totalXian δ + N.totalDead δ = N.totalR δ := by
  unfold totalAlive totalXian totalDead totalR
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (N.edgeQty δ i).h_conservation

-- 【D1 网络定律】四条合一（对单个网络）。
theorem d1_network_properties :
    Function.Surjective (N.nodeOf 0) ∧
    (∀ {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ → N.nodeCount δ₂ ≤ N.nodeCount δ₁) ∧
    (∀ i j : Fin κ, (N.nodeSetoid 0).r i j ↔ N.strength i = N.strength j) ∧
    (∀ δ : ℚ, N.totalAlive δ + N.totalXian δ + N.totalDead δ = N.totalR δ) :=
  ⟨N.nodeOf_surjective 0,
   fun h => N.nodeCount_antitone h,
   fun i j => N.node_zero_iff i j,
   fun δ => N.net_qty_pair_conservation δ⟩

-- ============ 完整持久同调：birth（barcode）与 death（节点合并） ============

/-
  【DiffNet = death 事件的结构】

  v189 证明了三界读数是差异谱的层析（barcode）——但那个 barcode **只有出生**：
  每个差异值 v 在阈值 δ 越过它时"出生"，然后永不死亡。
  这正是"读数只记得几个、不记得哪几个"的另一种说法。

  DiffNet 补上另一半：**合并**。
  网络里有两个差异对 i, j，强度分别是 strength i、strength j。
  在阈值 δ 下，若 |strength i − strength j| ≤ δ，它们被判为"同类"（step），
  于是落进同一个节点（nodeSetoid 的等价类）——这是一次合并，一个 death 事件。

  所以：
    · birth：谱值（v189 的 spectralDensity）；
    · death：强度差（这里的 step / nodeOf）；
    · 两者共享同一根 δ 轴，且都随 δ 增大而"粗化"：
        - 纵向（每个差异对内部）：更多差异值沉入死界；
        - 横向（差异对之间）：更多差异对被判同类。

  这就是完整的单参数持久同调：出生计数 + 合并结构。
-/

-- 单步合并：强度差 ≤ δ ⟹ 两个差异对落进同一节点（一个 death 事件）。
theorem nodeOf_eq_of_step {δ : ℚ} {i j : Fin κ} (h : N.step δ i j) :
    N.nodeOf δ i = N.nodeOf δ j :=
  Quotient.sound (Relation.ReflTransGen.single h)

-- 合并只增不减：δ 增大，节点只合并、不分裂。
theorem merge_monotone {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) {i j : Fin κ}
    (hij : (N.nodeSetoid δ₁).r i j) : (N.nodeSetoid δ₂).r i j :=
  reflTransGen_mono (fun a b hab => by
    unfold step at hab ⊢
    linarith) i j hij

-- 节点数不超过差异对数。
set_option linter.style.haveILetI false in
theorem nodeCount_le (δ : ℚ) : N.nodeCount δ ≤ κ := by
  unfold nodeCount
  letI := N.nodeDecidable δ
  have h := Fintype.card_quotient_le (N.nodeSetoid δ)
  simpa using h

-- 初始分量数（δ = 0）= 不同强度值的个数。
set_option linter.style.haveILetI false in
theorem nodeCount_zero_eq :
    N.nodeCount 0 = (Finset.univ.image N.strength).card := by
  unfold nodeCount
  letI := N.nodeDecidable 0
  letI : Fintype { v // v ∈ Finset.univ.image N.strength } :=
    Fintype.subtype (Finset.univ.image N.strength) (fun _ => Iff.rfl)
  let g : Quotient (N.nodeSetoid 0) → { v // v ∈ Finset.univ.image N.strength } :=
    Quot.lift
      (fun i => (⟨N.strength i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ :
        { v // v ∈ Finset.univ.image N.strength }))
      (fun i j h => Subtype.ext ((N.node_zero_iff i j).mp h))
  have hsurj : Function.Surjective g := by
    intro v
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp v.2
    exact ⟨Quotient.mk _ i, Subtype.ext hi⟩
  have hinj : Function.Injective g := by
    intro q1 q2 hq
    induction q1 using Quotient.ind with
    | _ i =>
      induction q2 using Quotient.ind with
      | _ j =>
        have hval : N.strength i = N.strength j := by
          have := congrArg Subtype.val hq
          simpa [g] using this
        exact Quotient.sound ((N.node_zero_iff i j).mpr hval)
  have h1 := Fintype.card_le_of_surjective g hsurj
  have h2 := Fintype.card_le_of_injective g hinj
  have hcoe : Fintype.card { v // v ∈ Finset.univ.image N.strength }
      = (Finset.univ.image N.strength).card :=
    Fintype.card_coe (Finset.univ.image N.strength)
  omega

-- 全合并：存在阈值 δ，使所有差异对落进同一节点。
theorem all_merged_of_range (hκ : 0 < κ) :
    ∃ δ : ℚ, ∀ i j : Fin κ, N.nodeOf δ i = N.nodeOf δ j := by
  have hne : (Finset.univ : Finset (Fin κ)).Nonempty :=
    ⟨⟨0, hκ⟩, Finset.mem_univ _⟩
  obtain ⟨mx, -, hmx⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin κ)) N.strength hne
  obtain ⟨mn, -, hmn⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin κ))
    (fun i => -N.strength i) hne
  refine ⟨N.strength mx - N.strength mn, ?_⟩
  intro i j
  apply N.nodeOf_eq_of_step
  unfold step
  rw [abs_sub_le_iff]
  have hmxi : N.strength i ≤ N.strength mx := hmx i (Finset.mem_univ i)
  have hmxj : N.strength j ≤ N.strength mx := hmx j (Finset.mem_univ j)
  have hmni : N.strength mn ≤ N.strength i := by
    linarith [hmn i (Finset.mem_univ i)]
  have hmnj : N.strength mn ≤ N.strength j := by
    linarith [hmn j (Finset.mem_univ j)]
  constructor <;> linarith

-- 【双轴粗化】同一根 δ 轴上，纵向（barcode）与横向（节点）同时变粗。
theorem double_axis {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    N.nodeCount δ₂ ≤ N.nodeCount δ₁ ∧
    (∀ i : Fin κ,
      sReading (N.left i) (N.right i) δ₂ ≤ sReading (N.left i) (N.right i) δ₁) :=
  ⟨N.nodeCount_antitone h, fun i => sReading_antitone (N.left i) (N.right i) h⟩

end DiffNet

-- ============ 守恒网络（多域）：总量是唯一的不变量 ============

/-
  【守恒网络：从"三读守恒"到"一族域的守恒"】

  量对讲的是三个域（生/暹/死）的守恒；D1 讲的是网络。把两者合起来：

    · 域族 = 有限的域索引 ι，每个域带一个**有符号**读数 v i
      （差异可以有正负——这正是相位的来源）；
    · 转移 = 从域 i 移一个单位到域 j（i ≠ j）；
    · 总量 = ∑ i, v i。

  两条定律：
    (1) 守恒：任何转移都保持总量——差异不消失，只换域；
    (2) 完备：总量相等 ⟹ 存在有限次转移把 v 变成 w。
        即 **总量是唯一的不变量**：守恒网络的连通分量恰好是等总量层。

  完备性这条是网络视角的关键：守恒不只是一个不变量，
  它是**全部**——在此之外没有别的不可达屏障。这是 D7 在网络层面的完整形态。
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- 网络总量（有符号读数之和）。
def netTotal (v : ι → ℤ) : ℤ := ∑ i, v i

-- 单步转移：从域 i 移一个单位到域 j（各引理均假设 i ≠ j）。
def consMove (v : ι → ℤ) (i j : ι) : ι → ℤ :=
  fun k => if k = i then v k - 1 else if k = j then v k + 1 else v k

-- 转移关系（一步）。
def ConsStep (v w : ι → ℤ) : Prop := ∃ i j, i ≠ j ∧ w = consMove v i j

omit [Fintype ι] in
theorem consMove_apply_i {v : ι → ℤ} {i j : ι} :
    consMove v i j i = v i - 1 := by
  unfold consMove
  simp

omit [Fintype ι] in
theorem consMove_apply_j {v : ι → ℤ} {i j : ι} (hij : i ≠ j) :
    consMove v i j j = v j + 1 := by
  unfold consMove
  have hji : ¬ (j = i) := fun h => hij h.symm
  simp [hji]

omit [Fintype ι] in
theorem consMove_apply_other {v : ι → ℤ} {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    consMove v i j k = v k := by
  unfold consMove
  simp [hki, hkj]

-- (1) 守恒：转移保持总量。
theorem consMove_total {v : ι → ℤ} {i j : ι} (hij : i ≠ j) :
    netTotal (consMove v i j) = netTotal v := by
  unfold netTotal
  have hfun : consMove v i j = fun k => v k + (if k = j then (1 : ℤ) else 0)
      - (if k = i then 1 else 0) := by
    funext k
    unfold consMove
    by_cases hki : k = i
    · subst hki
      have hkj : ¬ (k = j) := hij
      simp [hkj]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · simp [hki, hkj]
  rw [hfun, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : (∑ k, (if k = j then (1 : ℤ) else 0)) = 1 := by simp
  have h2 : (∑ k, (if k = i then (1 : ℤ) else 0)) = 1 := by simp
  rw [h1, h2]
  ring

theorem consStep_preserves_total {v w : ι → ℤ} (h : ConsStep v w) :
    netTotal w = netTotal v := by
  obtain ⟨i, j, hij, rfl⟩ := h
  exact consMove_total hij

-- 零和且有非零项 ⟹ 存在正项。
omit [DecidableEq ι] in
theorem exists_pos_of_sum_eq_zero {d : ι → ℤ} (hsum : ∑ i, d i = 0)
    (hne : ∃ i, d i ≠ 0) : ∃ i, 0 < d i := by
  by_contra h
  push Not at h
  have h0 : ∀ i, d i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => h i)).mp hsum i (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := hne
  exact hi (h0 i)

-- 零和且有非零项 ⟹ 存在负项。
omit [DecidableEq ι] in
theorem exists_neg_of_sum_eq_zero {d : ι → ℤ} (hsum : ∑ i, d i = 0)
    (hne : ∃ i, d i ≠ 0) : ∃ i, d i < 0 := by
  by_contra h
  push Not at h
  have h0 : ∀ i, d i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).mp hsum i (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := hne
  exact hi (h0 i)

-- 正部质量：负数截为 0 后的总质量（转移要消耗的"电量"）。
def posMass (d : ι → ℤ) : ℕ := ∑ i, (d i).toNat

-- 一次前进（盈余 i → 亏空 j）严格减少正部质量。
theorem posMass_lt_step {v w : ι → ℤ} {i j : ι} (hij : i ≠ j)
    (hi : 0 < v i - w i) (hj : v j - w j < 0) :
    posMass (consMove v i j - w) < posMass (v - w) := by
  unfold posMass
  simp only [Pi.sub_apply]
  apply Finset.sum_lt_sum
  · intro k _
    by_cases hki : k = i
    · have heq : consMove v i j k - w k = (v k - w k) - 1 := by
        rw [hki, consMove_apply_i]
        ring
      rw [heq, hki]
      exact Int.toNat_le_toNat (by linarith)
    · by_cases hkj : k = j
      · have heq : consMove v i j k - w k = (v k - w k) + 1 := by
          rw [hkj, consMove_apply_j hij]
          ring
        rw [heq, hkj, Int.toNat_of_nonpos (by linarith)]
        exact Nat.zero_le _
      · have heq : consMove v i j k = v k := consMove_apply_other hki hkj
        rw [heq]
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    have heq : consMove v i j i - w i = (v i - w i) - 1 := by
      rw [consMove_apply_i]
      ring
    rw [heq]
    exact (Int.toNat_lt_toNat (by linarith : (0 : ℤ) < v i - w i)).mpr (by linarith)

-- (2) 完备：总量相等 ⟹ 有限次转移连通（强归纳于正部质量）。
theorem cons_reachable {v w : ι → ℤ} (h : netTotal v = netTotal w) :
    Relation.ReflTransGen ConsStep v w := by
  have key : ∀ (M : ℕ) (v w : ι → ℤ), posMass (v - w) = M →
      netTotal v = netTotal w → Relation.ReflTransGen ConsStep v w := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
      intro v w hM htot
      by_cases hall : ∀ k, v k = w k
      · have hvw : v = w := funext hall
        rw [hvw]
      · have hne : ∃ k, v k - w k ≠ 0 := by
          by_contra h'
          push Not at h'
          exact hall (fun k => sub_eq_zero.mp (h' k))
        have hsum : ∑ k, (v k - w k) = 0 := by
          have hvw : ∑ k, v k = ∑ k, w k := htot
          rw [Finset.sum_sub_distrib]
          linarith
        obtain ⟨i, hi⟩ := exists_pos_of_sum_eq_zero hsum hne
        obtain ⟨j, hj⟩ := exists_neg_of_sum_eq_zero hsum hne
        have hij : i ≠ j := by
          intro heq
          subst heq
          linarith
        have htot' : netTotal (consMove v i j) = netTotal w := by
          rw [consMove_total hij]
          exact htot
        have hlt : posMass (consMove v i j - w) < M := by
          rw [← hM]
          exact posMass_lt_step hij hi hj
        have hrec := ih (posMass (consMove v i j - w)) hlt (consMove v i j) w rfl htot'
        exact Relation.ReflTransGen.head ⟨i, j, hij, rfl⟩ hrec
  exact key _ v w rfl h

-- 总量相等 ⟺ 有限次转移连通（守恒网络的连通分量 = 等总量层）。
theorem cons_reachable_iff {v w : ι → ℤ} :
    Relation.ReflTransGen ConsStep v w ↔ netTotal v = netTotal w := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (consStep_preserves_total hbc).symm
  · exact cons_reachable

-- 【守恒网络定理】守恒 + 完备：总量是唯一的不变量。
theorem conservation_network_theorem :
    (∀ (v w : ι → ℤ), ConsStep v w → netTotal w = netTotal v) ∧
    (∀ (v w : ι → ℤ), Relation.ReflTransGen ConsStep v w ↔ netTotal v = netTotal w) :=
  ⟨fun _ _ h => consStep_preserves_total h, fun _ _ => cons_reachable_iff⟩

-- ============ 守恒量的完全性：任何不变量都是总量的函数 ============

/-
  【唯一不变量 = 任何不变量都是它的函数】

  `cons_reachable_iff` 已经说：可达 ⟺ 同总量。这一条其实已经蕴含了
  "没有更细的不变量"——但要把它写成**函子式**陈述，还需要一步：

      若 I 在任何转移下不变，则 I 只依赖 netTotal。

  换句话说：守恒网络上的任何一个"守恒量"，都必然穿过 netTotal 分解。
  这就是"总量是**唯一**不变量"的精确含义——不是"唯一的不变量值"，
  而是"唯一的不变量维度"。

  再给一个规范形：把所有质量集中到一个域 i₀。每个状态都可达它的规范形，
  且规范形由总量唯一决定。于是**连通分量 ≅ ℤ**（通过 netTotal）——
  和"对位 ≅ ℚ"是同一手法：给每个等价类一个唯一的代表元。
-/

-- 沿转移链不变 ⟹ 端点相等。
omit [Fintype ι] in
theorem invariant_step_chain {β : Type*} (I : (ι → ℤ) → β)
    (hI : ∀ v w, ConsStep v w → I v = I w)
    {v w : ι → ℤ} (h : Relation.ReflTransGen ConsStep v w) : I v = I w := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hI _ _ hbc)

-- 任何在转移下不变的量，都是总量的函数。
theorem invariant_is_function_of_total {β : Type*} (I : (ι → ℤ) → β)
    (hI : ∀ v w, ConsStep v w → I v = I w) :
    ∀ v w, netTotal v = netTotal w → I v = I w :=
  fun _ _ htot => invariant_step_chain I hI (cons_reachable htot)

-- 规范形：把总质量全部集中到域 i₀。
def canon (i₀ : ι) (v : ι → ℤ) : ι → ℤ :=
  fun k => if k = i₀ then netTotal v else 0

-- 规范形的总量 = 原总量。
theorem canon_total (i₀ : ι) (v : ι → ℤ) : netTotal (canon i₀ v) = netTotal v := by
  unfold canon netTotal
  simp

-- 每个状态都可达它的规范形。
theorem cons_reachable_canon (i₀ : ι) (v : ι → ℤ) :
    Relation.ReflTransGen ConsStep v (canon i₀ v) :=
  cons_reachable (canon_total i₀ v).symm

-- 规范形相同 ⟺ 总量相同（canon 只在 i₀ 处放总量）。
theorem canon_eq_iff {i₀ : ι} {v w : ι → ℤ} :
    canon i₀ v = canon i₀ w ↔ netTotal v = netTotal w := by
  constructor
  · intro h
    have := congrFun h i₀
    simpa [canon] using this
  · intro h
    funext k
    by_cases hk : k = i₀
    · subst hk
      simp [canon, h]
    · simp [canon, hk]

-- 【总量完全性总纲】守恒 + 完备 + 唯一 + 规范形。
theorem total_is_complete_invariant (i₀ : ι) :
    (∀ (v w : ι → ℤ), ConsStep v w → netTotal w = netTotal v) ∧
    (∀ (v w : ι → ℤ), Relation.ReflTransGen ConsStep v w ↔ netTotal v = netTotal w) ∧
    (∀ {β : Type*} (I : (ι → ℤ) → β), (∀ (v w : ι → ℤ), ConsStep v w → I v = I w) →
      ∀ (v w : ι → ℤ), netTotal v = netTotal w → I v = I w) ∧
    (∀ v : ι → ℤ, Relation.ReflTransGen ConsStep v (canon i₀ v)) ∧
    (∀ (v w : ι → ℤ), Relation.ReflTransGen ConsStep v w ↔ canon i₀ v = canon i₀ w) :=
  ⟨fun _ _ h => consStep_preserves_total h,
   fun _ _ => cons_reachable_iff,
   fun I hI => invariant_is_function_of_total I hI,
   cons_reachable_canon i₀,
   fun v w => by rw [cons_reachable_iff, canon_eq_iff]⟩

-- ============ topos 站：有限极限与指数对象（Type 是初等 topos） ============

/-
  【有限 topos 站：不建 ∞-topos，只建**有限初等 topos** 的五条结构】

  Grothendieck 链是 site → 预层 → 层 → 几何。终点站是 topos。
  我们不追求一般 topos（那需要全部极限性质的统一打包），
  而是把初等 topos 的公理逐条在 Type 上**构造性地**证出来：

    ① 终对象：PUnit，任意 α → PUnit 唯一；
    ② 积（极限）：(γ → α × β) ≃ (γ → α) × (γ → β)；
    ③ 余积（余极限）：(α ⊕ β → γ) ≃ (α → γ) × (β → γ)；
    ④ 指数对象（幂）：(γ × α → β) ≃ (γ → α → β)（currying）；
    ⑤ 子对象分类器：Ω = Bool（有限/可判定版）——
       分辨空间 resolveSpace α 与有限子对象 Finset α 双射（resolveEquivFinset）。
    ⑥ 离散图的极限（有限积）：(γ → ∀ i, α i) ≃ (∀ i, γ → α i)。

  关于 ⑤：一般 topos 的分类器是 Ω = Prop，从任意单射的反向提取需要选择
  （Classical.choose）——这与"无 Classical"的底线冲突。有限/可判定世界里
  分类器就是 Ω = Bool，而"分辨 = α → Bool" 正是理论的分辨空间。
  所以这一步不是妥协，是有限性给出的**更好的分类器**：
  每一个可判定子对象都由唯一的分辨分类。

  ⑥ 是与守恒网络的接轨：守恒网络的状态空间 ι → ℤ 就是离散图（每个域一个 ℤ）
  的有限积。**多域守恒状态 = 有限积（极限）的元素**——守恒网络就是离散图
  在 Type 里的极限。这样 topos 站与前面的网络站由同一个极限概念扣在一起。
-/

-- ① 终对象：PUnit，任意 α → PUnit 的映射都唯一。
theorem terminal_uniq {α : Type*} (f g : α → PUnit) : f = g := by
  funext x
  exact Subsingleton.elim _ _

-- ② 积（极限）：给出 γ → α × β 等价于给出两个分量映射（积的泛性质）。
def prodUniversal (α β γ : Type*) : (γ → α × β) ≃ (γ → α) × (γ → β) where
  toFun f := (fun x => (f x).1, fun x => (f x).2)
  invFun p := fun x => (p.1 x, p.2 x)
  left_inv f := by
    funext x
    exact Prod.eta (f x)
  right_inv p := by
    cases p with
    | mk f g => rfl

-- ③ 余积（余极限）：给出 α ⊕ β → γ 等价于给出两个分量映射（余积的泛性质）。
def sumUniversal (α β γ : Type*) : (α ⊕ β → γ) ≃ (α → γ) × (β → γ) where
  toFun f := (fun a => f (Sum.inl a), fun b => f (Sum.inr b))
  invFun p := fun s => match s with
    | Sum.inl a => p.1 a
    | Sum.inr b => p.2 b
  left_inv f := by
    funext s
    cases s with
    | inl a => rfl
    | inr b => rfl
  right_inv p := by
    cases p with
    | mk f g => rfl

-- ④ 指数对象（幂）：currying 就是指数的泛性质（eval + 唯一分解）。
def expUniversal (α β γ : Type*) : (γ × α → β) ≃ (γ → α → β) where
  toFun f := fun c a => f (c, a)
  invFun g := fun p => g p.1 p.2
  left_inv f := by
    funext p
    cases p with
    | mk c a => rfl
  right_inv g := by
    funext c a
    rfl

-- ⑤ 子对象分类器（有限/可判定版）：Ω = Bool。
-- 每个分辨（α → Bool）分类一个有限子对象，且这是双射——
-- 可判定子对象的分类器就是理论的分辨空间本身。
theorem subobject_classifier_finite {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Bijective (fun p : resolveSpace α => Finset.univ.filter (fun a => p a = true)) :=
  resolveEquivFinset.bijective

-- ⑥ 离散图的极限（有限积）：全局映射族 ≃ 逐域映射族。
def piUniversal {ι : Type*} (α : ι → Type*) (γ : Type*) :
    (γ → ∀ i, α i) ≃ (∀ i, γ → α i) where
  toFun f := fun i c => f c i
  invFun g := fun c i => g i c
  left_inv f := by
    funext c i
    rfl
  right_inv g := by
    funext i c
    rfl

-- 守恒网络的状态空间 ι → ℤ = 离散图（每个域一个 ℤ）的有限积。
-- 多域守恒状态就是极限的元素：全局状态 ≃ 每个域各自的探测族。
def conservation_as_limit {ι : Type*} (γ : Type*) :
    (γ → ∀ _ : ι, ℤ) ≃ (∀ _ : ι, γ → ℤ) :=
  piUniversal (fun _ => ℤ) γ

-- ============ 第五层：自指驻留（EgoFixedPoint） ============

/-
  【第五层：自我 = 自映射的驻留】

  前四层（层/计数/动力学/对角线）各有自己的数据形状。第五层是它们共同的自指面：
  一个自映射 step : α → α，它的**驻留**（不动点）就是"自我"的最小模型。

  两种驻留形态（原文：税台与自我是同一件事的两种形态）：
    · 投影型（幂等）：step ∘ step = step。自我（reflect）、消解、凝结都是这一型。
      这一型必有驻留：step x 就在像上，而像上全是不动点。
    · 对合型（两次回原）：step ∘ step = id。税台（环反射）、半转都是这一型。
      这一型的存在性由奇偶决定（奇数基数保证有不动点，偶数可以没有）。

  而在有限世界里统摄两者的是一个更朴素的事实：
    **任何有限自映射都有最终周期点**（鸽笼原理）。
  不动点只是周期 1 的特例；"自指总有驻留或循环"——这是第五层的根定理。
-/

-- 驻留的两种形态。
inductive StasisKind where
  | projection   -- 幂等：做两次 = 一次
  | involution   -- 对合：做两次 = 恒等
  deriving DecidableEq

-- 自指驻留系统：一个自映射 + 它的形态 + 该形态的定律。
structure EgoFixedPoint (α : Type*) where
  step : α → α
  kind : StasisKind
  h_proj : kind = .projection → ∀ x, step (step x) = step x
  h_inv : kind = .involution → ∀ x, step (step x) = x

-- 投影型必有驻留（任何非空类型）：step x 就在像上，像上全是不动点。
theorem ego_projection_fixed {α : Type*} [Nonempty α] (step : α → α)
    (hidem : ∀ x, step (step x) = step x) : ∃ x, step x = x := by
  obtain ⟨x⟩ := ‹Nonempty α›
  exact ⟨step x, hidem x⟩

-- 投影型的驻留集就是像集（不动点在像上，像上全是不动点）。
theorem projection_fixed_iff_image {α : Type*} (step : α → α)
    (hidem : ∀ x, step (step x) = step x) (x : α) :
    step x = x ↔ ∃ y, step y = x := by
  constructor
  · intro h
    exact ⟨x, h⟩
  · rintro ⟨y, rfl⟩
    exact hidem y

-- 对合型 + 奇数基数 ⟹ 驻留存在（通用定理 exists_fixed_of_odd_card 的实例）。
theorem ego_involution_fixed_of_odd {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (step : α → α) (hinv : ∀ x, step (step x) = x) (hodd : Odd (Fintype.card α)) :
    ∃ x, step x = x :=
  exists_fixed_of_odd_card step hinv hodd

-- 【根定理】有限自映射必有最终周期点（鸽笼原理，构造性）。
theorem periodic_point_exists {α : Type*} [Fintype α] [Nonempty α] (f : α → α) :
    ∃ y, ∃ k : ℕ, 1 ≤ k ∧ f^[k] y = y := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have hlt : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by simp
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (Fintype.card α + 1) => f^[i.val] x) hlt
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with h | h
  · refine ⟨f^[i.val] x, j.val - i.val, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt h), heq]
  · refine ⟨f^[j.val] x, i.val - j.val, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt h)]
    exact heq

-- 自我：reflect 是投影型驻留（幂等）。
theorem reflect_idempotent (d : DifferenceObject) :
    DifferenceObject.reflect (DifferenceObject.reflect d) = DifferenceObject.reflect d :=
  (DifferenceObject.reflect_fixed_point_iff_stable (DifferenceObject.reflect d)).mpr
    (DifferenceObject.reflect_stable d)

-- 环反射对任意 m（包括 m = 0 的空情形）都是对合。
theorem ringReflect_involutive_all (m : ℕ) :
    ∀ k : Fin m, ringReflect m (ringReflect m k) = k := by
  intro k
  apply Fin.ext
  show m - 1 - (m - 1 - k.val) = k.val
  have := k.isLt
  omega

universe u

-- 【第五层定理】两形态的驻留 + 有限性的根定理。
theorem fifth_layer_theorem :
    (∀ (α : Type u) [Nonempty α] (step : α → α), (∀ x, step (step x) = step x) →
      ∃ x, step x = x) ∧
    (∀ (α : Type u) [Fintype α] [DecidableEq α] [LinearOrder α] (f : α → α),
      (∀ x, f (f x) = x) → Odd (Fintype.card α) → ∃ x, f x = x) ∧
    (∀ (α : Type u) [Fintype α] [Nonempty α] (f : α → α),
      ∃ y, ∃ k : ℕ, 1 ≤ k ∧ f^[k] y = y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α _ step hstep
    exact ego_projection_fixed step hstep
  · intro α _ _ _ f hinv hodd
    exact ego_involution_fixed_of_odd f hinv hodd
  · intro α _ _ f
    exact periodic_point_exists f

-- ============ EgoSystem：第五层的偏差版（dev 与驻留的合流） ============

/-
  【EgoSystem：把 kind 与 dev 合流】

  EgoFixedPoint 用 kind（投影/对合）刻画驻留；DifferenceObject 用 dev（偏差）刻画稳定。
  合流成一个结构：

      EgoSystem α = step : α → α, dev : α → ℚ, 固定点 ⟺ dev = 0。

  于是：
    · 自我（reflect）给出实例（固定 ⟺ 偏差为零 ⟺ s/r = n）；
    · 收缩（dev 减半）⟹ 迭代收敛（复用 ContractingSystem 的构造性收敛）；
    · 投影型的像点必稳定（像即驻留集，dev = 0）；
    · 未稳定时有限步永不归零（"转即稳定，停即死"的 EgoSystem 版）。
-/

structure EgoSystem (α : Type*) where
  step : α → α
  dev : α → ℚ
  h_fixed : ∀ x, step x = x ↔ dev x = 0

namespace EgoSystem

variable {α : Type*}

-- 稳定点迭代不变（停在原处）。
theorem iter_fixed_of_stable (S : EgoSystem α) {x : α} (hx : S.dev x = 0) :
    ∀ k : ℕ, S.step^[k] x = x := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, (S.h_fixed x).mpr hx]

-- 投影型：像点必稳定（像即驻留集，dev = 0）。
theorem projection_image_stable (S : EgoSystem α)
    (hidem : ∀ x, S.step (S.step x) = S.step x) (x : α) :
    S.dev (S.step x) = 0 :=
  (S.h_fixed (S.step x)).mp (hidem x)

-- 收缩 EgoSystem = ContractingSystem（自动实例化，复用构造性收敛）。
def toContracting (S : EgoSystem α) (h : ∀ x, S.dev (S.step x) = S.dev x / 2) :
    ContractingSystem where
  state := α
  step := S.step
  dev := S.dev
  h_shrink := h

-- 收缩 ⟹ 构造性收敛：任意 ε > 0，有限步内偏差小于 ε。
theorem converges (S : EgoSystem α) (h : ∀ x, S.dev (S.step x) = S.dev x / 2)
    (x : α) {ε : ℚ} (hε : 0 < ε) :
    ∃ k : ℕ, |S.dev ((S.toContracting h).iter k x)| < ε :=
  ContractingSystem.dev_converges (S.toContracting h) x hε

-- 未稳定时有限步永不归零（"转即稳定，停即死"）。
theorem iter_never_stable (S : EgoSystem α)
    (h : ∀ x, S.dev (S.step x) = S.dev x / 2) {x : α} (hx : S.dev x ≠ 0) (k : ℕ) :
    S.dev (S.step^[k] x) ≠ 0 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply', h]
    exact div_ne_zero ih (by norm_num)

end EgoSystem

-- ============ 第五层统一结构：kind + dev ============

/-
  【EgoFull：第五层的最终合流】

  驻留有两种语言：kind（投影 / 对合）与 dev（偏差归零）。
  EgoFixedPoint 用 kind 说话，EgoSystem 用 dev 说话。这里合成一个结构：

      step + kind + dev + 三条定律（固定 ⟺ dev=0；投影幂等；对合回原）。

  两种实例：
    · 自我：投影型 + 真实偏差 dev = s/r − n；
    · 税台：对合型 + 驻留指示偏差 dev = （驻留 ? 0 : 1）。

  于是"驻留 = 偏差归零"对两种形态同时成立：
    · 自我稳定 ⟺ s/r = n；
    · 奇数环上税台必有一个 dev = 0 的点（对合型的存在性由奇偶决定）。
-/

-- EgoFull = EgoSystem 加一个 kind 标签。dev 语言完全由 EgoSystem 承载，
-- kind 只说明步函数是投影还是对合（附加的两条定律）。
structure EgoFull (α : Type*) extends EgoSystem α where
  kind : StasisKind
  h_proj : kind = .projection → ∀ x, step (step x) = step x
  h_inv : kind = .involution → ∀ x, step (step x) = x

namespace EgoFull

variable {α : Type*}

-- 丢掉 dev，只留 kind：EgoFull 是 EgoFixedPoint 再加一层偏差语言。
def toFixedPoint (E : EgoFull α) : EgoFixedPoint α :=
  ⟨E.step, E.kind, E.h_proj, E.h_inv⟩

end EgoFull

-- 自我：投影型 + 真实偏差（s/r − n）。
def egoSelfFull : EgoFull DifferenceObject where
  toEgoSystem :=
    { step := DifferenceObject.reflect
      dev := DifferenceObject.deviation
      h_fixed := fun d => (DifferenceObject.reflect_fixed_point_iff_stable d).trans
        (DifferenceObject.stable_iff_deviation_zero d).symm }
  kind := .projection
  h_proj := fun _ d => reflect_idempotent d
  h_inv := fun h => by cases h

-- 税台：对合型 + 驻留指示偏差（驻留 0，非驻留 1）。
def egoTaxFull (m : ℕ) : EgoFull (Fin m) where
  toEgoSystem :=
    { step := ringReflect m
      dev := fun k => if ringReflect m k = k then 0 else 1
      h_fixed := fun k => by
        by_cases h : ringReflect m k = k
        · rw [ite_eq_left h]
          exact ⟨fun _ => rfl, fun _ => h⟩
        · rw [ite_eq_right h]
          constructor
          · intro hk
            exact absurd hk h
          · intro h0
            exact absurd h0 (by norm_num) }
  kind := .involution
  h_proj := fun h => by cases h
  h_inv := fun _ k => ringReflect_involutive_all m k

-- 自我驻留 ⟺ 雪球平衡（统一结构版）。
theorem egoSelf_zero_dev (d : DifferenceObject) :
    egoSelfFull.dev d = 0 ↔ d.ratio = d.n :=
  DifferenceObject.stable_iff_deviation_zero d

-- 税台驻留存在（奇数环）：对合型的偏差在某点归零。
theorem egoTax_zero_dev {m : ℕ} (hm : 0 < m) (hodd : Odd m) :
    ∃ k : Fin m, (egoTaxFull m).dev k = 0 := by
  obtain ⟨k, hk⟩ := ringReflect_fixed_of_odd hm hodd
  exact ⟨k, ((egoTaxFull m).h_fixed k).mp hk⟩

-- 【第五层统一】两种驻留形态共用"驻留 = 偏差归零"。
theorem fifth_layer_unified :
    (∀ d : DifferenceObject, egoSelfFull.dev d = 0 ↔ d.ratio = d.n) ∧
    (∀ m : ℕ, 0 < m → Odd m → ∃ k : Fin m, (egoTaxFull m).dev k = 0) :=
  ⟨egoSelf_zero_dev, fun m hm hodd => egoTax_zero_dev (m := m) hm hodd⟩

-- 第五层 kind 版的实例：由统一结构投影而来——kind 只是 EgoFull 的一半。
def egoSelf : EgoFixedPoint DifferenceObject := egoSelfFull.toFixedPoint

def egoTax (m : ℕ) : EgoFixedPoint (Fin m) := (egoTaxFull m).toFixedPoint

-- ============ 桥：sheaf 层 ↔ topos（层塔的极限 = 最细层对象） ============

/-
  【sheaf 层的极限站：全局截面 = 相容族 = 最细层数据】

  topos 站建好了极限（离散图的有限积）。层链这边的 sheaf 公理说：
  "局部相容 ⟹ 唯一粘合"。这条公理在范畴论里的精确形态就是**极限**：

      全局截面 → ∏_层 局部截面 ⇉ ∏_{细≤粗} 粗层读数

  在有限分辨层塔上，这个极限可以算出来：
    · 一个"相容族" = 每层一个凝结对象，且粗层读数是细层的消解像；
    · 层塔的消解是商的投影塔（不是一般的图），所以**整个相容族由最细层
      的那个对象唯一决定**——粗层全是它的消解像；
    · 反过来，最细层的任何对象都长出一个相容族（沿塔逐层消解）。

  于是：**层塔的极限 ≅ 最细层对象**。
  这就是 sheaf 层与 topos 站之间的显式桥：sheaf 的"局部数据粘合"
  在有限商塔上就是极限，而极限在这里坍缩成最细层——
  因为商塔的每张粗图都只是细图的像，没有额外的粘合障碍。
-/

namespace LayerLadder

-- 在层塔上，i ≤ j（i 更粗）⟹ δ j ≤ δ i（j 更细，阈值更小）。
theorem le_delta (L : LayerLadder) {i j : Fin L.m} (h : i ≤ j) : L.δ j ≤ L.δ i := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (L.h_dec hlt)
  · rcases heq
    exact le_rfl

-- 最细层的索引：层的最后一个台阶（δ 严格递减，所以它是阈值最小的一层）。
def finest (L : LayerLadder) (hm : 0 < L.m) : Fin L.m :=
  ⟨L.m - 1, by omega⟩

end LayerLadder

-- 层塔的相容族：每层一个凝结对象，且粗层读数是细层的消解像。
-- 这就是层塔图的"极限对象"（全局截面）。
def towerLimit (L : LayerLadder) (n : ℕ) : Type :=
  { f : ∀ i : Fin L.m, ResLayer.object ⟨L.δ i⟩ n //
      ∀ (i j : Fin L.m) (h : i ≤ j),
        ResLayer.resolution (L.le_delta h) (f j) = f i }

-- 消解在恒等层上是恒等（对任意等价性证明成立）。
theorem resolution_refl {δ : ℚ} {n : ℕ} (q : ResLayer.object ⟨δ⟩ n) :
    ResLayer.resolution (le_refl δ) q = q := by
  simp [ResLayer.resolution_id]

-- 最细层对象 → 相容族：沿塔逐层消解。
def ladderToLimit (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    (x : ResLayer.object ⟨L.δ (L.finest hm)⟩ n) : towerLimit L n :=
  ⟨fun i => ResLayer.resolution (L.le_delta (by
      show i.val ≤ (L.finest hm).val
      have hf : (L.finest hm).val = L.m - 1 := rfl
      rw [hf]
      have := i.isLt
      omega)) x, by
    intro i j hij
    rw [ResLayer.resolution_comp]⟩

-- 相容族 → 最细层对象：取最细层的分量。
def limitToFinest (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    (f : towerLimit L n) : ResLayer.object ⟨L.δ (L.finest hm)⟩ n :=
  f.1 (L.finest hm)

-- 【桥定理】层塔的极限（相容族）≅ 最细层对象。
def ladderLimitEquiv (L : LayerLadder) (hm : 0 < L.m) (n : ℕ) :
    towerLimit L n ≃ ResLayer.object ⟨L.δ (L.finest hm)⟩ n where
  toFun := limitToFinest L hm
  invFun := ladderToLimit L hm
  left_inv f := by
    apply Subtype.ext
    funext i
    exact f.2 i (L.finest hm) (by
      show i.val ≤ (L.finest hm).val
      have hf : (L.finest hm).val = L.m - 1 := rfl
      rw [hf]
      have := i.isLt
      omega)
  right_inv x := by
    unfold limitToFinest ladderToLimit
    exact resolution_refl x

-- 【sheaf ↔ topos 桥】层塔的全局截面对象与最细层对象同构：
-- 局部数据的唯一粘合由最细层唯一决定，粗层只是它的消解像。
theorem sheaf_topos_bridge (L : LayerLadder) (hm : 0 < L.m) (n : ℕ) :
    Nonempty (towerLimit L n ≃ ResLayer.object ⟨L.δ (L.finest hm)⟩ n) :=
  ⟨ladderLimitEquiv L hm n⟩

-- ============ 层塔的 Mittag-Leffler 条件：坍缩的原因 ============

/-
  【为什么层塔的极限坍缩到最细层？】

  v174 证了 towerLimit ≅ finest（sheaf_topos_bridge）。这里补上"为什么"：
  **每一层的消解都是满射**。

  满射塔（Mittag-Leffler 条件）的逆极限是平凡的：
  相容族里每个粗层分量都被细层分量"打满"，
  没有额外的选择自由，所以整个相容族由最细层唯一决定。

  反过来说，如果某层消解不是满射，就会出现"细层没有、粗层有"的元素，
  逆极限就会多出维度——那才是真正的"新粘合障碍"。
  消解是 Quotient.map id，id 满射 ⟹ 消解满射——这就是全部原因。
-/

-- （消解的满射性即 v174 的 ResLayer.resolution_surjective，此处直接引用。）

-- 【Mittag-Leffler 坍缩】满射塔的极限 = 最细层（含满射性原因）。
theorem mittag_leffler_collapse (L : LayerLadder) (hm : 0 < L.m) (n : ℕ) :
    (∀ (i j : Fin L.m) (h : i ≤ j),
        Function.Surjective (ResLayer.resolution (n := n) (L.le_delta h))) ∧
      Nonempty (towerLimit L n ≃ ResLayer.object ⟨L.δ (L.finest hm)⟩ n) :=
  ⟨fun _ _ h => ResLayer.resolution_surjective (L.le_delta h),
   ⟨ladderLimitEquiv L hm n⟩⟩

-- ============ 投影算子 π 的多规则层版本 ============

/-
  【π 的多规则版：投影规则 = 三界视角】

  原文的投影算子 π_{k→k+n}：取层 k 上构成对象的**同一组差异对**，
  用层 k+n 的规则重新凝结——"不可见差异对不在 𝒦 的输入里"。

  所以 π 的本质不是"换个阈值看一眼"，而是**选一条规则决定哪些差异对进入输入**。
  有限世界里恰好有三条自然规则（就是三界）：

    · .living   ：只收差异 > δ 的对（生界规则，原文的严格投影）；
    · .visible  ：收差异 ≥ δ 的对（生界 + 暹界）；
    · .allRules ：全收（含死界，即完整的底层材料）。

  三条规则的读数之差，恰好是量对的三读：

      读数(.living)  = s                       （生界）
      读数(.visible) = s + j                   （生 + 暹）
      读数(.allRules)= r = s + j + d           （全部）
      读数(.visible) 与 读数(.allRules) 之差 = d（死界）

  另：原文说"消解像与自身投影的差异来自中间层的额外过滤"。
  在 filter 模型里，中间层的过滤是**幂等**的（filter 复合律），
  所以逐步消解像 = 直接投影——中间层不产生额外过滤。
  这正是 r 在差异对层面为 0 的原因：要让它非零，必须换规则，
  而不能只靠多走几层。
-/

-- 投影规则（三界视角）。
inductive ProjRule where
  | living    -- 只收生界（差异 > δ）
  | visible   -- 生界 + 暹界（差异 ≥ δ）
  | allRules  -- 全部差异对（含死界）
  deriving DecidableEq

-- 规则 r 在阈值 δ 下，强度为 s 的差异对是否进入投影输入。
def keptBy (r : ProjRule) (δ : ℚ) (s : ℚ) : Prop :=
  match r with
  | .living => δ < s
  | .visible => δ ≤ s
  | .allRules => True

-- 规则可判定（构造性：ℚ 的比较可判定）。
instance keptBy_decidable (r : ProjRule) (δ : ℚ) : DecidablePred (keptBy r δ) := by
  intro s
  cases r with
  | living => exact (inferInstance : Decidable (δ < s))
  | visible => exact (inferInstance : Decidable (δ ≤ s))
  | allRules => exact (inferInstance : Decidable True)

-- 投影读数：规则 r 下，层 δ 上进入投影输入的差异对数。
def projReading {m n : ℕ} (r : ProjRule) (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (min m n) => keptBy r δ |pairDiff x y i|)).card

-- 生界规则 = s 读（原文的严格投影）。
theorem projReading_living {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .living x y δ = sReading x y δ := by
  unfold projReading sReading aliveSet
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  exact Iff.rfl

-- 可见规则 = 生 + 暹。
theorem projReading_visible {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .visible x y δ = sReading x y δ + xianReading x y δ := by
  unfold projReading sReading xianReading aliveSet xianSet
  have hunion : (Finset.univ.filter (fun i : Fin (min m n) => keptBy .visible δ |pairDiff x y i|))
      = (Finset.univ.filter (fun i : Fin (min m n) => δ < |pairDiff x y i|))
        ∪ (Finset.univ.filter (fun i : Fin (min m n) => |pairDiff x y i| = δ)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    show (δ ≤ |pairDiff x y i|) ↔ (δ < |pairDiff x y i| ∨ |pairDiff x y i| = δ)
    constructor
    · intro hi
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq.symm
    · rintro (h | h)
      · exact le_of_lt h
      · exact le_of_eq h.symm
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (min m n) => δ < |pairDiff x y i|))
      (Finset.univ.filter (fun i : Fin (min m n) => |pairDiff x y i| = δ)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    linarith
  rw [hunion, Finset.card_union_of_disjoint hdisj]

-- 全收规则 = 公共域 r（全部底层材料）。
theorem projReading_all {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .allRules x y δ = r_rel x y := by
  unfold projReading r_rel
  have h : (Finset.univ.filter (fun i : Fin (min m n) => keptBy .allRules δ |pairDiff x y i|))
      = Finset.univ.filter (fun _ : Fin (min m n) => True) := by
    apply Finset.filter_congr
    intro i _
    exact ⟨fun _ => trivial, fun _ => trivial⟩
  rw [h, Finset.filter_true]
  simp

-- 规则单调：生界 ≤ 可见 ≤ 全部。
theorem projReading_mono {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .living x y δ ≤ projReading .visible x y δ ∧
      projReading .visible x y δ ≤ projReading .allRules x y δ := by
  constructor
  · rw [projReading_living, projReading_visible]
    omega
  · rw [projReading_visible, projReading_all]
    have h := qty_pair_conservation x y δ
    omega

-- 规则账本：全收 − 可见 = 死界读数。
theorem projReading_ledger {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .allRules x y δ = projReading .visible x y δ + dReading x y δ := by
  rw [projReading_all, projReading_visible]
  have h := qty_pair_conservation x y δ
  omega

-- 中间层不过滤：逐步投影（生界规则）等于直接投影。
-- 这是"消解像 = 自身投影"在 filter 层面的精确形式，也是 r 在差异对层面为 0 的原因。
theorem proj_stepwise_eq_direct {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    (Finset.univ.filter (fun i : Fin (min m n) =>
        keptBy .living δ₁ |pairDiff x y i| ∧ keptBy .living δ₂ |pairDiff x y i|))
      = (Finset.univ.filter (fun i : Fin (min m n) => keptBy .living δ₂ |pairDiff x y i|)) := by
  apply Finset.filter_congr
  intro i _
  show (δ₁ < |pairDiff x y i| ∧ δ₂ < |pairDiff x y i|) ↔ δ₂ < |pairDiff x y i|
  constructor
  · intro hi
    exact hi.2
  · intro hi
    exact ⟨lt_of_le_of_lt h hi, hi⟩

-- 【多规则投影定理】三条规则的读数 = 三界读数，规则差 = 量对差。
theorem multi_rule_projection {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .living x y δ = sReading x y δ ∧
    projReading .visible x y δ = sReading x y δ + xianReading x y δ ∧
    projReading .allRules x y δ = r_rel x y ∧
    projReading .allRules x y δ = projReading .visible x y δ + dReading x y δ :=
  ⟨projReading_living x y δ, projReading_visible x y δ, projReading_all x y δ,
   projReading_ledger x y δ⟩

-- ============ 观测即管理：规则族与阈值族互为参数化 ============

/-
  【观测即管理：选规则 ≡ 调阈值】

  π 多规则版说：投影的读数是"选一条规则"决定的（三界视角）。
  δ 管理说：读数是"选一个阈值"决定的（归约到 manageThresholds）。

  这两件事在原文里像是两套旋钮。但 ℚ 的稠密性让它们**完全互相模拟**：

    (1) 可见规则 @ δ  =  生界规则 @ δ'（δ' 略低于 δ）
        只要 δ' 落在"δ 下方最近的差异值"和 δ 之间，没有差异值跨过 δ'，
        两个 filter 就是同一批维度。ℚ 稠密 ⟹ 这样的 δ' 总存在。

    (2) 生界规则 @ δ  =  可见规则 @ δ'（δ' 略高于 δ）
        对称地，δ' 落在 δ 和"δ 上方最近的差异值"之间即可。

    (3) 全收规则 是常数，= 生界规则 @ (−1)（所有差异值都 > −1）。

  于是三条规则不是"另外一套观测"，而是**同一族读数在阈值轴上的三个位置**：
  换规则 ≡ 把阈值挪进某个间隙里。这就是"观测即管理"——

      观测（选规则）不是去看一个新世界，而是把管理参数（阈值）挪一格。

  反过来也成立（(2)），所以这不是单向嵌入，是真正的相互参数化。
  关键在于：能这么挪，恰恰因为 ℚ **无限可分**（v181 的"无穷可分"
  在这里第一次派上用场——稠密性 ⟹ 间隙永远存在）。
-/

-- 差异值集合：所有公共维度的差异绝对值（有限）。
def diffVals {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : Finset ℚ :=
  Finset.univ.image (fun i : Fin (min m n) => |pairDiff x y i|)

-- 【间隙引理·下侧】δ 下方总有一个"安全阈值"：
-- 它严格小于 δ，且对每个差异值 v，判据 `δ' < v` 与 `δ ≤ v` 完全一致。
theorem exists_lower_gap {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    ∃ δ' : ℚ, δ' < δ ∧ ∀ i : Fin (min m n),
      (δ' < |pairDiff x y i| ↔ δ ≤ |pairDiff x y i|) := by
  by_cases hne : ((diffVals x y).filter (fun v => v < δ)).Nonempty
  · obtain ⟨m₀, hm₀mem, hm₀max⟩ := Finset.exists_max_image _ id hne
    have hm₀lt : m₀ < δ := (Finset.mem_filter.mp hm₀mem).2
    refine ⟨(δ + m₀) / 2, by linarith, ?_⟩
    intro i
    constructor
    · intro hlt
      by_contra hnot
      have hdlt : |pairDiff x y i| < δ := not_le.mp hnot
      have hmem : |pairDiff x y i| ∈ (diffVals x y).filter (fun v => v < δ) :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hdlt⟩
      have hle : |pairDiff x y i| ≤ m₀ := hm₀max _ hmem
      linarith
    · intro hle
      linarith
  · refine ⟨δ - 1, by linarith, ?_⟩
    intro i
    constructor
    · intro hlt
      by_contra hnot
      have hdlt : |pairDiff x y i| < δ := not_le.mp hnot
      have hmem : |pairDiff x y i| ∈ (diffVals x y).filter (fun v => v < δ) :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hdlt⟩
      exact absurd ⟨_, hmem⟩ hne
    · intro hle
      linarith

-- 【间隙引理·上侧】对称地，δ 上方总有一个"安全阈值"。
theorem exists_upper_gap {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    ∃ δ' : ℚ, δ < δ' ∧ ∀ i : Fin (min m n),
      (δ < |pairDiff x y i| ↔ δ' ≤ |pairDiff x y i|) := by
  by_cases hne : ((diffVals x y).filter (fun v => δ < v)).Nonempty
  · obtain ⟨m₀, hm₀mem, hm₀min⟩ := Finset.exists_max_image _ (fun v : ℚ => -v) hne
    have hm₀gt : δ < m₀ := (Finset.mem_filter.mp hm₀mem).2
    refine ⟨(δ + m₀) / 2, by linarith, ?_⟩
    intro i
    constructor
    · intro hlt
      have hmem : |pairDiff x y i| ∈ (diffVals x y).filter (fun v => δ < v) :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hlt⟩
      have := hm₀min _ hmem
      linarith
    · intro hle
      by_contra hnot
      have hdle : |pairDiff x y i| ≤ δ := not_lt.mp hnot
      linarith
  · refine ⟨δ + 1, by linarith, ?_⟩
    intro i
    constructor
    · intro hlt
      have hmem : |pairDiff x y i| ∈ (diffVals x y).filter (fun v => δ < v) :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hlt⟩
      exact absurd ⟨_, hmem⟩ hne
    · intro hle
      linarith

-- 【规则 → 阈值】可见规则 @ δ = 生界规则 @ δ'（δ' 略低于 δ）。
theorem visible_eq_living_gap {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    ∃ δ' : ℚ, δ' < δ ∧ projReading .visible x y δ = projReading .living x y δ' := by
  obtain ⟨δ', hlt, hiff⟩ := exists_lower_gap x y δ
  refine ⟨δ', hlt, ?_⟩
  unfold projReading
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp only [keptBy]
  exact (hiff i).symm

-- 【阈值 → 规则】生界规则 @ δ = 可见规则 @ δ'（δ' 略高于 δ）。
theorem living_eq_visible_gap {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    ∃ δ' : ℚ, δ < δ' ∧ projReading .living x y δ = projReading .visible x y δ' := by
  obtain ⟨δ', hgt, hiff⟩ := exists_upper_gap x y δ
  refine ⟨δ', hgt, ?_⟩
  unfold projReading
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp only [keptBy]
  exact hiff i

-- 【全收规则归位】全收规则是常数 = 生界规则 @ (−1)。
theorem all_eq_living_neg {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .allRules x y δ = projReading .living x y (-1) := by
  rw [projReading_all, projReading_living, sReading_neg_one]

-- 规则无差别 ⟺ 暹界为空（δ 不是有效阈值）。
theorem rules_agree_iff {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .living x y δ = projReading .visible x y δ ↔ xianReading x y δ = 0 := by
  rw [projReading_living, projReading_visible]
  omega

-- 阈值管理的归约（threshold_reduction）直接提升到规则读数。
theorem rule_threshold_reduction {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    ∃ δ' ∈ manageThresholds x y, projReading .living x y δ' = projReading .living x y δ := by
  obtain ⟨δ', hmem, heq⟩ := threshold_reduction x y δ
  exact ⟨δ', hmem, by simp only [projReading_living]; exact heq⟩

-- 【观测即管理·主定理】规则族与阈值族互为参数化。
theorem observation_is_management {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    (∀ δ : ℚ, ∃ δ' : ℚ, δ' < δ ∧ projReading .visible x y δ = projReading .living x y δ') ∧
    (∀ δ : ℚ, ∃ δ' : ℚ, δ < δ' ∧ projReading .living x y δ = projReading .visible x y δ') ∧
    (∀ δ : ℚ, projReading .allRules x y δ = projReading .living x y (-1)) :=
  ⟨fun δ => visible_eq_living_gap x y δ,
   fun δ => living_eq_visible_gap x y δ,
   fun δ => all_eq_living_neg x y δ⟩

-- 【观测即管理·总纲】规则差 = 暹界读数；换规则 ≡ 挪阈值。
theorem observation_management_theorem {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    -- (a) 规则之差恰是暹界读数
    (∀ δ : ℚ, projReading .visible x y δ
        = projReading .living x y δ + xianReading x y δ) ∧
    -- (b) 规则无差别 ⟺ 暹界为空（δ 不在有效阈值上）
    (∀ δ : ℚ, (projReading .living x y δ = projReading .visible x y δ
        ↔ xianReading x y δ = 0)) ∧
    -- (c) 可见规则 = 生界规则在略低阈值；生界规则 = 可见规则在略高阈值
    (∀ δ : ℚ, ∃ δ' : ℚ, δ' < δ ∧ projReading .visible x y δ = projReading .living x y δ') ∧
    (∀ δ : ℚ, ∃ δ' : ℚ, δ < δ' ∧ projReading .living x y δ = projReading .visible x y δ') ∧
    -- (d) 全收规则是常数 = 生界规则 @ −1
    (∀ δ : ℚ, projReading .allRules x y δ = projReading .living x y (-1)) :=
  ⟨fun δ => projReading_visible x y δ,
   fun δ => rules_agree_iff x y δ,
   fun δ => visible_eq_living_gap x y δ,
   fun δ => living_eq_visible_gap x y δ,
   fun δ => all_eq_living_neg x y δ⟩

-- ============ 一般分类器：可行性考察 ============

/-
  【一般分类器能做多细？】

  三界规则（living/visible/allRules）只是三种**特别自然**的分类器。
  一般情形下，一个"投影分类器"就是任意选一批差异对进入输入：

      S ∈ Finset (Fin (min m n))    （共 2^k 种，k = min m n）

  它的读数就是 |S|。本区块问：一般分类器比三界规则多出什么？

  答案是**两极**：

    · 在"多少"上，一般分类器确实更细：读数可以取 0..k 的每一个值
      （classifier_reaches_all_readings），三界规则在固定 δ 下只占三个点。

    · 在"哪几个"上，一般分类器一元所有：读数只记得 |S|，
      完全丢掉了 S 是谁。这正是计数读数的先天盲区，也是 D1 的
      "点是残影"在分类器层面的回声——读数比点更残。

  所以"一般分类器"在差异论里不是不可行，而是**在读数层面塌缩成基数**：
  它没有带来新的读数维度，只带来新的"选法"。若要它真的可见，
  必须换一个不丢 S 的读数（组合数据、纠缠、相位）——而那是另一层的事。

  另：分类器的补 Sᶜ 就是"互补填洞"——读数 k − |S|（量对守恒的又一形态）。
-/

-- 一般投影分类器：任意选一批差异对进入输入，读数是基数。
def genericReading {k : ℕ} (S : Finset (Fin k)) : ℕ := S.card

-- 有限集的基数不超过宇宙基数（Fin k 上）。
theorem finset_card_fin_le {k : ℕ} (S : Finset (Fin k)) : S.card ≤ k := by
  have h := Finset.card_le_card (Finset.subset_univ S)
  simpa using h

-- 读数谱全像：一般分类器能读出 0..k 的每一个值。
theorem classifier_reaches_all_readings {k : ℕ} :
    (Finset.univ.image (fun S : Finset (Fin k) => genericReading S))
      = Finset.range (k + 1) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range, genericReading]
  constructor
  · rintro ⟨S, rfl⟩
    have h := finset_card_fin_le S
    omega
  · intro hj
    have hj' : j ≤ k := by omega
    refine ⟨(Finset.univ : Finset (Fin j)).image (Fin.castLE hj'), ?_⟩
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hj')]
    simp

-- 分类器的补 = 互补填洞：|S| + |Sᶜ| = k。
theorem generic_reading_complement {k : ℕ} (S : Finset (Fin k)) :
    genericReading S + genericReading Sᶜ = k := by
  unfold genericReading
  have hle : S.card ≤ k := finset_card_fin_le S
  have h := Finset.card_compl (s := S)
  simp only [Fintype.card_fin] at h
  omega

-- 任何规则的读数都不超过公共维度数（谱 [0, k]）。
theorem projReading_le (r : ProjRule) {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    (δ : ℚ) : projReading r x y δ ≤ min m n := by
  unfold projReading
  have h : (Finset.univ.filter
      (fun i : Fin (min m n) => keptBy r δ |pairDiff x y i|)).card
      ≤ (Finset.univ : Finset (Fin (min m n))).card :=
    Finset.card_le_card (Finset.subset_univ _)
  simpa using h

-- 三界规则的读数都落在谱 [0, k] 内（三条特别分类器 = 谱上三个点）。
theorem three_rules_in_spectrum {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .living x y δ ≤ min m n ∧
      projReading .visible x y δ ≤ min m n ∧
      projReading .allRules x y δ ≤ min m n :=
  ⟨projReading_le .living x y δ, projReading_le .visible x y δ,
   projReading_le .allRules x y δ⟩

-- 【一般分类器·边界】读数层面：一般分类器可达全部读数，但只记得基数；
-- 补分类器守恒（互补填洞）。
theorem general_classifier_boundary {k : ℕ} :
    (Finset.univ.image (fun S : Finset (Fin k) => genericReading S)) = Finset.range (k + 1) ∧
    (∀ S : Finset (Fin k), genericReading S + genericReading Sᶜ = k) :=
  ⟨classifier_reaches_all_readings, fun S => generic_reading_complement S⟩

-- ============ 阈值族 vs 规则族：完整的刻画 ============

/-
  【哪些分类器能被阈值产生？】

  v186 说三条自然规则（living/visible/allRules）都能被阈值模拟；
  v187 说一般分类器（任意子集 S）最多只能读出基数。

  这里给出完整的答案：**一个规则 S 能被某个阈值 δ 产生，
  当且仅当 S 对差异值"上闭"**——即若 i ∈ S 且 v i ≤ v j，则 j ∈ S。

  也就是说：阈值族 = 规则族里的"单调"那部分。

    · 阈值族 ⊆ 规则族：每个 δ 给一个规则（超水平集）；
    · 规则族 → 阈值族：只有上闭的能做到；
    · 严格包含：min m n ≥ 2 时，"只选差异最小的那对"是上闭的反例。

  这是"观测即管理"的边界刻画：管理（选 δ）只能产生**单调**的观测；
  非单调的观测（比如"只盯住差异最小的那对"）必须直接指定规则，
  不能由阈值产生。管理是"从高到低扫一刀"，规则可以是"任意挖一块"。
-/

-- 阈值产生的规则：差异值严格大于 δ 的维度（超水平集）。
def thresholdSet {k : ℕ} (v : Fin k → ℚ) (δ : ℚ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => δ < v i)

-- 上闭：若 i 在集合里，任何差异值不小于 v i 的维度也在。
def UpwardClosed {k : ℕ} (v : Fin k → ℚ) (S : Finset (Fin k)) : Prop :=
  ∀ i ∈ S, ∀ j, v i ≤ v j → j ∈ S

-- 【刻画】S 是阈值集 ⟺ S 上闭。
theorem threshold_iff_upward_closed {k : ℕ} (hk : 0 < k) (v : Fin k → ℚ)
    (S : Finset (Fin k)) :
    (∃ δ : ℚ, S = thresholdSet v δ) ↔ UpwardClosed v S := by
  constructor
  · rintro ⟨δ, rfl⟩ i hi j hj
    unfold thresholdSet at hi ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  · intro hup
    unfold UpwardClosed at hup
    by_cases huniv : S = Finset.univ
    · rw [huniv]
      have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      obtain ⟨mn, -, hmn⟩ :=
        Finset.exists_max_image (Finset.univ : Finset (Fin k)) (fun i => -v i) hne
      refine ⟨v mn - 1, ?_⟩
      ext i
      simp only [thresholdSet, Finset.mem_filter, Finset.mem_univ, true_and, true_iff]
      linarith [hmn i (Finset.mem_univ i)]
    · have hex : ∃ j, j ∉ S := by
        by_contra h
        push Not at h
        exact huniv (Finset.eq_univ_iff_forall.mpr h)
      obtain ⟨j₀, hj₀⟩ := hex
      let T := (Finset.univ : Finset (Fin k)).filter (fun j => j ∉ S)
      have hTne : T.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
      obtain ⟨mx, hmxmem, hmx⟩ := Finset.exists_max_image T v hTne
      refine ⟨v mx, ?_⟩
      ext i
      simp only [thresholdSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        by_contra h
        push Not at h
        exact (Finset.mem_filter.mp hmxmem).2 (hup i hi mx h)
      · intro hlt
        by_contra hi
        have : v i ≤ v mx := hmx i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        linarith

-- 阈值族严格小于规则族（k ≥ 2 时）：存在不上闭的规则。
theorem threshold_family_strict {k : ℕ} (hk : 2 ≤ k) :
    ∃ (v : Fin k → ℚ) (S : Finset (Fin k)), ¬ UpwardClosed v S := by
  refine ⟨fun i => (i : ℚ), {⟨0, by omega⟩}, ?_⟩
  intro hup
  have hi : (⟨0, by omega⟩ : Fin k) ∈ ({⟨0, by omega⟩} : Finset (Fin k)) :=
    Finset.mem_singleton.mpr rfl
  have hj : (⟨1, by omega⟩ : Fin k) ∈ ({⟨0, by omega⟩} : Finset (Fin k)) :=
    hup ⟨0, by omega⟩ hi ⟨1, by omega⟩ (by simp)
  rw [Finset.mem_singleton] at hj
  exact absurd hj (by simp)

-- ============ 三界读数 = 差异谱的层析（persistence barcode） ============

/-
  【三界读数 = 差异谱的层析】

  一个差异对象在公共维度上给出一个**谱**：每个维度的差异绝对值
  |d_i|（i < min m n）。这是一个有限多重集——同一个值可以出现多次。

  三界读数逐层读这个谱：

      sReading δ = #{i : |d_i| > δ}    （生界：还没落地的差异）
      xianReading δ = #{i : |d_i| = δ}  （暹界：恰好压在阈值上的差异）
      dReading δ = #{i : |d_i| < δ}    （死界：已经沉没的差异）

  这正是**持续性（persistence）**的层析：把阈值 δ 从大到小扫过去，
  每越过一个谱值，就有若干"bar"从生界落进死界。

  对照拓扑数据分析（TDA）：
    · 一个 barcode 是一堆积压的区间，每个阈值上"活着"的 bar 数是一个台阶函数；
    · 这里 sReading 就是"活着"的 bar 数，xianReading 是"恰好此刻落地"的 bar 数，
      dReading 是"已死"的 bar 数；
    · 而 s + j + d = r 就是 **bar 的总数守恒**（谱的总质量 = 公共维度数）。

  两次"合流"在这里合成一次：

    (A) 观测即管理（v186）说：任何阈值都能挪进差异值之间的间隙。
        这里它变成**重构定理的核心工具**——
        正因为间隙永远存在，才能用"略低于 v 的某个 δ"读出"≥ v 的计数"，
        从而从 sReading 的完整剖面反推出每个谱值的重数。

    (B) 一般分类器边界（v187）说：读数只记得"几个"，不记得"哪几个"。
        在 barcode 语言里就是：**这个 barcode 只有出生、没有合并**。
        真正的持久同调需要知道"谁和谁合并"（death 事件），
        而"谁和谁"正是 DiffNet 的等价关系（nodeSetoid）该提供的信息。

  一句话：三界读数是差异谱的层析；它记住了 barcode 的"出生计数"，
  丢掉了"合并结构"——而这恰好解释了为什么 v187 的读数会塌缩成基数。
-/

-- 差异谱的密度：每个差异值 v 出现多少次（= 暹界读数）。
def spectralDensity {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (v : ℚ) : ℕ :=
  xianReading x y v

-- 谱的总质量守恒：所有差异值的重数之和 = 公共维度数（barcode 的 bar 总数）。
theorem spectral_total {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    ∑ v ∈ diffVals x y, spectralDensity x y v = min m n := by
  unfold spectralDensity xianReading xianSet
  rw [← Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin (min m n))))
    (t := diffVals x y)
    (f := fun i : Fin (min m n) => |pairDiff x y i|)
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
  simp

-- "≥ δ" 层的基数（生界 + 暹界）——它就是可见规则的读数。
def countGE {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (min m n) => δ ≤ |pairDiff x y i|)).card

-- ≥ δ 的计数就是可见规则读数。
theorem countGE_eq_projReading {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    countGE x y δ = projReading .visible x y δ := by
  unfold countGE projReading keptBy
  rfl

-- ≥ δ 的计数 = 生界 + 暹界。
theorem countGE_eq {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    countGE x y δ = sReading x y δ + xianReading x y δ := by
  rw [countGE_eq_projReading, projReading_visible]

-- δ 是 v 的"安全下界"时（没有差异值落在 [δ, v) 里），"≥ v"的计数就是"生界 @ δ"。
theorem countGE_eq_sReading_of_safe {m n : ℕ} (x : StateQuant m) (y : StateQuant n)
    {δ v : ℚ} (hlt : δ < v)
    (h : ∀ i : Fin (min m n), ¬ (δ ≤ |pairDiff x y i| ∧ |pairDiff x y i| < v)) :
    countGE x y v = sReading x y δ := by
  unfold countGE sReading aliveSet
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  constructor
  · intro hle
    by_contra hnot
    have hdle : |pairDiff x y i| ≤ δ := not_lt.mp hnot
    linarith
  · intro hgt
    by_contra hnot
    have hltv : |pairDiff x y i| < v := not_le.mp hnot
    exact h i ⟨le_of_lt hgt, hltv⟩

-- 两个对象的共同安全下界：取它们所有差异值中"低于 v 的最大者"与 v 的中点。
theorem exists_common_safe {m n m' n' : ℕ} (x : StateQuant m) (y : StateQuant n)
    (x' : StateQuant m') (y' : StateQuant n') (v : ℚ) :
    ∃ δ : ℚ, δ < v ∧
      (∀ i : Fin (min m n), ¬ (δ ≤ |pairDiff x y i| ∧ |pairDiff x y i| < v)) ∧
      (∀ i : Fin (min m' n'), ¬ (δ ≤ |pairDiff x' y' i| ∧ |pairDiff x' y' i| < v)) := by
  let S := ((diffVals x y) ∪ (diffVals x' y')).filter (fun u => u < v)
  by_cases hne : S.Nonempty
  · obtain ⟨m₀, hm₀mem, hm₀max⟩ := Finset.exists_max_image S id hne
    have hm₀lt : m₀ < v := (Finset.mem_filter.mp hm₀mem).2
    refine ⟨(m₀ + v) / 2, by linarith, ?_, ?_⟩
    · intro i hconj
      have hmem : |pairDiff x y i| ∈ S :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)),
           hconj.2⟩
      have hle : |pairDiff x y i| ≤ m₀ := hm₀max _ hmem
      linarith [hconj.1]
    · intro i hconj
      have hmem : |pairDiff x' y' i| ∈ S :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)),
           hconj.2⟩
      have hle : |pairDiff x' y' i| ≤ m₀ := hm₀max _ hmem
      linarith [hconj.1]
  · refine ⟨v - 1, by linarith, ?_, ?_⟩
    · intro i hconj
      have hmem : |pairDiff x y i| ∈ S :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)),
           hconj.2⟩
      exact absurd ⟨_, hmem⟩ hne
    · intro i hconj
      have hmem : |pairDiff x' y' i| ∈ S :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)),
           hconj.2⟩
      exact absurd ⟨_, hmem⟩ hne

-- 【重构定理】三界读数的完整剖面（所有阈值上）唯一决定差异谱：
-- 每个差异值的重数都由 sReading 的剖面逼出来。
theorem xianReading_determined_by_sReading {m n m' n' : ℕ}
    (x : StateQuant m) (y : StateQuant n) (x' : StateQuant m') (y' : StateQuant n')
    (h : ∀ δ : ℚ, sReading x y δ = sReading x' y' δ) :
    ∀ v : ℚ, xianReading x y v = xianReading x' y' v := by
  intro v
  obtain ⟨δ, hlt, hs1, hs2⟩ := exists_common_safe x y x' y' v
  have e1 : countGE x y v = sReading x y δ := countGE_eq_sReading_of_safe x y hlt hs1
  have e2 : countGE x' y' v = sReading x' y' δ := countGE_eq_sReading_of_safe x' y' hlt hs2
  have hc : countGE x y v = countGE x' y' v := by rw [e1, e2, h δ]
  have g1 : xianReading x y v + sReading x y v = countGE x y v := by
    rw [countGE_eq]
    omega
  have g2 : xianReading x' y' v + sReading x' y' v = countGE x y v := by
    rw [hc, countGE_eq]
    omega
  have hsum : xianReading x y v + sReading x y v
      = xianReading x' y' v + sReading x' y' v := by
    rw [g1, g2]
  rw [h v] at hsum
  exact Nat.add_right_cancel hsum

-- 反过来：谱（各值重数）决定生界读数（按层求和）。
theorem sReading_eq_sum_density {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    sReading x y δ = ∑ v ∈ diffVals x y, (if δ < v then xianReading x y v else 0) := by
  unfold sReading aliveSet
  rw [Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun i : Fin (min m n) => δ < |pairDiff x y i|))
    (t := diffVals x y)
    (f := fun i : Fin (min m n) => |pairDiff x y i|)
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
  refine Finset.sum_congr rfl ?_
  intro v _
  by_cases hδ : δ < v
  · rw [ite_eq_left hδ]
    unfold xianReading xianSet
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨_, h2⟩
      exact h2
    · intro h2
      exact ⟨by rw [h2]; exact hδ, h2⟩
  · rw [ite_eq_right hδ, Finset.card_eq_zero, Finset.filter_filter]
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hconj
    exact hδ (hconj.2 ▸ hconj.1)

-- 谱相同 ⟹ 生界读数相同（barcode 相同 ⟹ 层析相同）。
theorem sReading_eq_of_xian_eq {m n m' n' : ℕ}
    (x : StateQuant m) (y : StateQuant n) (x' : StateQuant m') (y' : StateQuant n')
    (hd : diffVals x y = diffVals x' y')
    (h : ∀ v : ℚ, xianReading x y v = xianReading x' y' v) :
    ∀ δ : ℚ, sReading x y δ = sReading x' y' δ := by
  intro δ
  rw [sReading_eq_sum_density, sReading_eq_sum_density, hd]
  apply Finset.sum_congr rfl
  intro v _
  rw [h v]

-- 【谱 ⟺ 读数】读数的完整剖面与差异谱互为唯一决定。
theorem readings_determine_spectrum {m n m' n' : ℕ}
    (x : StateQuant m) (y : StateQuant n) (x' : StateQuant m') (y' : StateQuant n')
    (hd : diffVals x y = diffVals x' y') :
    (∀ δ : ℚ, sReading x y δ = sReading x' y' δ) ↔
      (∀ v : ℚ, xianReading x y v = xianReading x' y' v) :=
  ⟨xianReading_determined_by_sReading x y x' y',
   fun h => sReading_eq_of_xian_eq x y x' y' hd h⟩

-- 【层析总纲】总质量守恒 + 层计数分解 + 三界守恒（bar 总数 = 公共维度数）。
theorem readings_are_level_profile {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    (∑ v ∈ diffVals x y, spectralDensity x y v = min m n) ∧
    (∀ δ : ℚ, countGE x y δ = sReading x y δ + xianReading x y δ) ∧
    (∀ δ : ℚ, sReading x y δ + xianReading x y δ + dReading x y δ = r_rel x y) :=
  ⟨spectral_total x y, fun δ => countGE_eq x y δ, fun δ => qty_pair_conservation x y δ⟩

-- ============ 完整持久同调：birth（barcode）+ death（节点合并） ============

/-
  【完整持久同调：两根腿终于接上】

  v189 给出 barcode（birth）：三界读数是差异谱的层析，但只有出生计数。
  DiffNet 给出合并（death）：强度差 ≤ δ ⟹ 同一节点。

  两者共用同一根 δ 轴。`full_persistence` 把四条事实打成一包：

    (1) birth：每个差异对的谱总质量 = 公共维度数（层析守恒）；
    (2) death：单步强度差 ≤ δ ⟹ 同节点（合并事件）；
    (3) 全合并：存在阈值使所有差异对同类（barcode 终将被抹平）；
    (4) 双轴：δ 增大时，纵向（生界读数）与横向（节点数）同时减少。

  于是"读数是 barcode 的出生计数，DiffNet 是 barcode 的合并结构"不再是比喻，
  而是四条定理的合取。
-/

theorem full_persistence {κ n : ℕ} (N : DiffNet κ n) (hκ : 0 < κ) :
    (∀ i : Fin κ, ∑ v ∈ diffVals (N.left i) (N.right i),
        spectralDensity (N.left i) (N.right i) v = n) ∧
    (∀ {δ : ℚ} {i j : Fin κ}, N.step δ i j → N.nodeOf δ i = N.nodeOf δ j) ∧
    (∃ δ : ℚ, ∀ i j : Fin κ, N.nodeOf δ i = N.nodeOf δ j) ∧
    (∀ i : Fin κ, ∀ {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ →
        N.nodeCount δ₂ ≤ N.nodeCount δ₁ ∧
        sReading (N.left i) (N.right i) δ₂ ≤ sReading (N.left i) (N.right i) δ₁) :=
  ⟨fun i => by simpa using spectral_total (N.left i) (N.right i),
   fun h => N.nodeOf_eq_of_step h,
   N.all_merged_of_range hκ,
   fun i δ₁ δ₂ hle =>
     ⟨N.nodeCount_antitone hle, sReading_antitone (N.left i) (N.right i) hle⟩⟩

-- ============ 多参数：一维投影不够（契诃夫的猎枪） ============

/-
  【契诃夫的猎枪：为什么那些层迟早要一起响】

  v189 说三界读数是差异谱的层析（barcode）。但那个 barcode 是**一维**的：
  一根 δ 轴，从高到低扫过去。

  而理论里堆了不止一根轴：
    · δ（层阈值）
    · τ_c（相变阈值，v191）
    · n（稳定目标，量对）
    · 每个对象自己的 δ（TypedStateQuant，D_typed 用 min x.δ y.δ）
    · 维度的索引（pairDiff 的 i）
    · 相位（positive / negative / neutral）

  单参数时，这些轴可以"排队"处理：一个扫完再扫下一个。
  但一旦有两条轴需要**同时**扫，事情就变了：

      **一维投影不决定二维结构。**

  这不是技术困难，是信息论的事实。下面这个定理是它的最小形式：
  两个"配对"可以有一模一样的一维谱，但二维格子里的点分布不同。

    · 一维谱 = 每个对象各自的差异谱（v189 的 spectralDensity）；
    · 配对结构 = 两个对象的哪些差异互相配对；
    · 单参数读数（s/r、barcode）只看到一维投影，看不到配对。

  所以"对位的完整信息是二维的，s/r 是它的一维投影"——
  这正是 v176 的"对位 ≅ ℚ"在多参数下的反面：
  在那个问题里，商掉分母得到有理数是对的；
  但商掉的东西在二维问题里会回来找你。

  这就是契诃夫的猎枪：所有那些层，不是叙事的装饰，是**参数**。
  单参数时它们可以在背景里等着；多参数时它们全部同时上场。
-/

-- 一维点投影：值 v 在 x 轴出现几次。
def xCount (P : Finset (ℚ × ℚ)) (v : ℚ) : ℕ :=
  (P.filter (fun p => p.1 = v)).card

-- 一维点投影：值 w 在 y 轴出现几次。
def yCount (P : Finset (ℚ × ℚ)) (w : ℚ) : ℕ :=
  (P.filter (fun p => p.2 = w)).card

-- 二维点计数：点 (v, w) 出现几次。
def xyCount (P : Finset (ℚ × ℚ)) (v w : ℚ) : ℕ :=
  (P.filter (fun p => p.1 = v ∧ p.2 = w)).card

-- 【一维投影不够】存在两个配对，一维谱完全相同，二维分布不同。
theorem point_projection_not_sufficient :
    ∃ P Q : Finset (ℚ × ℚ),
      (∀ v, xCount P v = xCount Q v) ∧
      (∀ w, yCount P w = yCount Q w) ∧
      ∃ v w, xyCount P v w ≠ xyCount Q v w := by
  refine ⟨({((0 : ℚ), (0 : ℚ)), (1, 1)} : Finset (ℚ × ℚ)),
          ({(0, 1), (1, 0)} : Finset (ℚ × ℚ)), ?_, ?_, ⟨0, 0, ?_⟩⟩
  · intro v
    unfold xCount
    by_cases hv0 : v = 0
    · subst hv0; decide
    · by_cases hv1 : v = 1
      · subst hv1; decide
      · have hP : ({(0, 0), (1, 1)} : Finset (ℚ × ℚ)).filter (fun p => p.1 = v) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact fun h => hv0 h.symm
          · exact fun h => hv1 h.symm
        have hQ : ({(0, 1), (1, 0)} : Finset (ℚ × ℚ)).filter (fun p => p.1 = v) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact fun h => hv0 h.symm
          · exact fun h => hv1 h.symm
        rw [hP, hQ]
  · intro w
    unfold yCount
    by_cases hw0 : w = 0
    · subst hw0; decide
    · by_cases hw1 : w = 1
      · subst hw1; decide
      · have hP : ({(0, 0), (1, 1)} : Finset (ℚ × ℚ)).filter (fun p => p.2 = w) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact fun h => hw0 h.symm
          · exact fun h => hw1 h.symm
        have hQ : ({(0, 1), (1, 0)} : Finset (ℚ × ℚ)).filter (fun p => p.2 = w) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact fun h => hw1 h.symm
          · exact fun h => hw0 h.symm
        rw [hP, hQ]
  · unfold xyCount
    decide

-- ============ 检验：D_typed 的二维是否退化成单参数 ============

/-
  【D_typed 的一维性：为什么它退化】

  TypedStateQuant 给每个对象自己的分辨率 δ。
  两个对象相遇时，D_typed 用 min x.δ y.δ —— 看起来是"两个参数"。

  但它退化成一维，原因是双重的：

    (1) min 是一维压缩：两个 δ 只以"较小者"的形式进入；
    (2) 更根本的：commonDist 本身就是一维的——它是 pairDiff 的平方和，
        把每一维的差异压成一个数。

  所以 D_typed 完全由 (commonDist, min δ, 两个相位) 决定：
  两个对象各自的 δ 只要 min 相同，就给出同一个干涉结果。

  这不是 bug，是"相互差异"的固有形状：
  一对对象之间的**对称**关系天然是一个数。
  要真二维，必须保留**逐维差异**（pairDiff），那就是 v189 的谱。

  所以"契诃夫的猎枪"在 D_typed 这里没有响——因为 D_typed 走的是
  对称的一维通道；它会在 pairDiff 那边响，因为那里每一维都是独立参数。
-/

-- D_typed 只依赖 min δ 和 mutual distance（不依赖两个 δ 的分别取值）。
theorem D_typed_determined_by_min {n : ℕ} (x y x' y' : TypedStateQuant n)
    (hcd : commonDist x.toStateQuant y.toStateQuant
        = commonDist x'.toStateQuant y'.toStateQuant)
    (hδ : min x.δ y.δ = min x'.δ y'.δ)
    (hph1 : x.toStateQuant.phase = x'.toStateQuant.phase)
    (hph2 : y.toStateQuant.phase = y'.toStateQuant.phase) :
    D_typed x y = D_typed x' y' := by
  unfold D_typed D
  rw [hcd, hδ, hph1, hph2]

-- 退化见证：第二个对象的 δ 可以随便换，只要 min 不变，结果不变。
theorem D_typed_loses_delta {n : ℕ} (x y : TypedStateQuant n) {d : ℚ}
    (h : min x.δ y.δ = min x.δ d) :
    D_typed x y = D_typed x ⟨d, y.toStateQuant⟩ := by
  unfold D_typed
  rw [h]

-- commonDist 就是 pairDiff 的平方和（一维投影）。
theorem commonDist_eq_sum_sq {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    commonDist x y = ∑ i : Fin (min m n), (pairDiff x y i) ^ 2 := by
  unfold commonDist pairDiff commonDim
  rfl

-- 平方和丢失方向：ℚ² 上，不同的向量可以有同一个平方和。
theorem sq_sum_not_injective :
    ∃ a b a' b' : ℚ,
      a ^ 2 + b ^ 2 = a' ^ 2 + b' ^ 2 ∧ (a, b) ≠ (a', b') :=
  ⟨1, 0, 0, 1, by norm_num⟩

-- 【检验结论】D_typed 走一维通道；真二维在 pairDiff 那边。
theorem typed_is_one_dimensional :
    (∀ {n : ℕ} (x y x' y' : TypedStateQuant n),
      commonDist x.toStateQuant y.toStateQuant
          = commonDist x'.toStateQuant y'.toStateQuant →
      min x.δ y.δ = min x'.δ y'.δ →
      x.toStateQuant.phase = x'.toStateQuant.phase →
      y.toStateQuant.phase = y'.toStateQuant.phase →
      D_typed x y = D_typed x' y') ∧
    (∀ {m n : ℕ} (x : StateQuant m) (y : StateQuant n),
      commonDist x y = ∑ i : Fin (min m n), (pairDiff x y i) ^ 2) ∧
    (∃ a b a' b' : ℚ, a ^ 2 + b ^ 2 = a' ^ 2 + b' ^ 2 ∧ (a, b) ≠ (a', b')) :=
  ⟨fun x y x' y' => D_typed_determined_by_min x y x' y',
   fun x y => commonDist_eq_sum_sq x y,
   sq_sum_not_injective⟩

-- ============ 二维持久：不可分解的最小例子 ============

/-
  【真二维：Casson–Zomorodian 的最小不可分解】

  v195 说 D_typed 退化成一维（对称通道）。
  但逐维通道是真的二维。这一节证明：**二维持久模一般不分解**——
  这是多参数持久同调最硬的数学事实（Carlsson–Zomorodian 2009）。

  格子：2×2 的点 (i,j) ∈ Fin 2 × Fin 2。
  一个"二维持久模"给每对 a ≤ b 一个秩 rank(V(a) → V(b))。
  若它可分解成"矩形区间" [p,q] 的直和，秩就能写成非负的区间计数和：

      rank(a,b) = Σ_{p ≤ a, b ≤ q} c(p,q),   c(p,q) ≥ 0。

  Casson–Zomorodian 的秩图案：所有 a ≤ b 的秩是 1，
  除了"从非 (1,1) 到 (1,1)"（那些映射是零映射，秩 0）。

  它不可能由非负区间计数实现——因为 c((0,0),(0,0)) 被迫为 -1。
  所以它**不可分解**。

  这就是"契诃夫的猎枪"在多参数下真正响的地方：
  不是单参数 barcode 的推广，而是一个新现象——
  有些结构本质上比任何一维区间全集都丰富。
-/

abbrev GridPoint : Type := Fin 2 × Fin 2

-- 秩函数：覆盖区间 [a,b] 的矩形区间总数（带重数）。
def intervalRank (c : GridPoint → GridPoint → ℤ) (a b : GridPoint) : ℤ :=
  if a ≤ b then
    ∑ p : GridPoint, ∑ q : GridPoint,
      (if (p ≤ a ∧ b ≤ q) then c p q else 0)
  else 0

-- Casson–Zomorodian 的秩图案。
def czRank (a b : GridPoint) : ℤ :=
  if a ≤ b then (if b = (1, 1) ∧ a ≠ (1, 1) then 0 else 1) else 0

-- 网格上只有 (0,0) 能 ≤ (0,0)。
private theorem le_zero_gridpoint {p : GridPoint} (h : p ≤ (0, 0)) : p = (0, 0) := by
  obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp h
  have e1 : p.1 = 0 := Fin.ext (Nat.le_zero.mp (Fin.le_def.mp h1))
  have e2 : p.2 = 0 := Fin.ext (Nat.le_zero.mp (Fin.le_def.mp h2))
  exact Prod.ext e1 e2

-- 第一行：a = (0,0) 时，rank 只由 q ≥ b 的区间贡献。
theorem intervalRank_zero_row (c : GridPoint → GridPoint → ℤ) (b : GridPoint) :
    intervalRank c (0, 0) b = ∑ q : GridPoint, (if b ≤ q then c (0, 0) q else 0) := by
  unfold intervalRank
  have h0b : (0, 0) ≤ b := by
    obtain ⟨i, j⟩ := b
    exact Prod.mk_le_mk.mpr ⟨Fin.zero_le _, Fin.zero_le _⟩
  rw [ite_eq_left h0b]
  rw [Finset.sum_eq_single (0, 0)]
  · apply Finset.sum_congr rfl
    intro q _
    simp
  · intro p _ hp
    have hnot : ¬ p ≤ (0, 0) := fun h => hp (le_zero_gridpoint h)
    simp only [hnot, false_and, ite_false, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

-- 【不可分解的核心】任何实现 czRank 的区间计数，必让 (0,0)-(0,0) 的计数为 -1。
theorem cz_forced_negative (c : GridPoint → GridPoint → ℤ)
    (h : ∀ a b, intervalRank c a b = czRank a b) :
    c (0, 0) (0, 0) = -1 := by
  -- rank((0,0),(1,1)) = 0 ⟹ c((0,0),(1,1)) = 0
  have e11 : c (0, 0) (1, 1) = 0 := by
    have hh := h (0, 0) (1, 1)
    rw [intervalRank_zero_row] at hh
    have hcz : czRank (0, 0) (1, 1) = 0 := by unfold czRank; simp
    rw [hcz] at hh
    rw [Finset.sum_eq_single (1, 1)] at hh
    · simpa using hh
    · intro q _ hq
      have hnot : ¬ (1, 1) ≤ q := by
        intro hle
        obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp hle
        have b1 : q.1.val ≤ 1 := by have := q.1.isLt; omega
        have b2 : q.2.val ≤ 1 := by have := q.2.isLt; omega
        have e1 : q.1 = 1 := Fin.ext (by have := Fin.le_def.mp h1; omega)
        have e2 : q.2 = 1 := Fin.ext (by have := Fin.le_def.mp h2; omega)
        exact hq (Prod.ext e1 e2)
      simp [hnot]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  -- rank((0,0),(1,0)) = 1 ⟹ c((0,0),(1,0)) + 0 = 1
  have e10 : c (0, 0) (1, 0) = 1 := by
    have hh := h (0, 0) (1, 0)
    rw [intervalRank_zero_row] at hh
    have hcz : czRank (0, 0) (1, 0) = 1 := by unfold czRank; simp
    rw [hcz] at hh
    rw [Fintype.sum_prod_type] at hh
    simp only [Fin.sum_univ_two] at hh
    norm_num at hh
    omega
  -- rank((0,0),(0,1)) = 1 ⟹ c((0,0),(0,1)) + 0 = 1
  have e01 : c (0, 0) (0, 1) = 1 := by
    have hh := h (0, 0) (0, 1)
    rw [intervalRank_zero_row] at hh
    have hcz : czRank (0, 0) (0, 1) = 1 := by unfold czRank; simp
    rw [hcz] at hh
    rw [Fintype.sum_prod_type] at hh
    simp only [Fin.sum_univ_two] at hh
    norm_num at hh
    omega
  -- rank((0,0),(0,0)) = 1 ⟹ c00 + c10 + c01 + c11 = 1
  have e00 : c (0, 0) (0, 0) + c (0, 0) (1, 0) + c (0, 0) (0, 1)
      + c (0, 0) (1, 1) = 1 := by
    have hh := h (0, 0) (0, 0)
    rw [intervalRank_zero_row] at hh
    have hcz : czRank (0, 0) (0, 0) = 1 := by unfold czRank; simp
    rw [hcz] at hh
    rw [Fintype.sum_prod_type] at hh
    simp only [Fin.sum_univ_two] at hh
    norm_num at hh
    omega
  omega

-- 【不可分解】不存在非负的区间计数实现 czRank。
theorem cz_not_interval_decomposable :
    ¬ ∃ c : GridPoint → GridPoint → ℤ,
      (∀ p q, 0 ≤ c p q) ∧
      (∀ a b, intervalRank c a b = czRank a b) := by
  rintro ⟨c, hnonneg, h⟩
  have hneg := cz_forced_negative c h
  have := hnonneg (0, 0) (0, 0)
  omega

-- ============ 可分解的正面：不可分解不是普遍的 ============

/-
  【判别问题的实质：有些可分解，有些不可】

  v196 证明了 Casson–Zomorodian 的秩图案不可分解。
  但这不意味着"二参数都不可分解"——恰恰相反，**绝大多数**是可分解的，
  不可分解是特殊形状。

  判别标准就是 Möbius 反演：
  秩图案可分解 ⟺ 区间计数 c 非负 ⟺ 秩图案是"非负矩形的和"。

  在 2×2 格上，第一行的 c 由四个秩值给出：
    c(00,11) = ρ(00,11)
    c(00,10) = ρ(00,10) − ρ(00,11)
    c(00,01) = ρ(00,01) − ρ(00,11)
    c(00,00) = ρ(00,00) − ρ(00,10) − ρ(00,01) + ρ(00,11)
  （这正是 cz_forced_negative 用的四个值。）

  所以"多参数强项"的精确问题不是"能不能分解"，而是：
  **理论的参数关系会把秩图案推到判别线的哪一侧？**

  下面先给一个正面的落点：常数秩（单个区间）可分解。
-/

-- 格内点 ≤ (1,1)。
private theorem le_top_gridpoint (b : GridPoint) : b ≤ (1, 1) := by
  obtain ⟨i, j⟩ := b
  exact Prod.mk_le_mk.mpr
    ⟨by have := i.isLt; simp only [Fin.le_def]; omega,
     by have := j.isLt; simp only [Fin.le_def]; omega⟩

-- 常数秩 = 单个区间 [(0,0),(1,1)]，可分解。
theorem constant_rank_decomposable :
    ∃ c : GridPoint → GridPoint → ℤ,
      (∀ p q, 0 ≤ c p q) ∧
      (∀ a b, intervalRank c a b = if a ≤ b then 1 else 0) := by
  refine ⟨fun p q => if p = (0, 0) ∧ q = (1, 1) then 1 else 0, ?_, ?_⟩
  · intro p q
    dsimp only
    split_ifs <;> norm_num
  · intro a b
    unfold intervalRank
    by_cases hab : a ≤ b
    · rw [ite_eq_left hab, ite_eq_left hab]
      rw [Finset.sum_eq_single (0, 0)]
      · rw [Finset.sum_eq_single (1, 1)]
        · rw [ite_eq_left (show (0, 0) ≤ a ∧ b ≤ (1, 1) from
            ⟨Prod.mk_le_mk.mpr ⟨Fin.zero_le _, Fin.zero_le _⟩, le_top_gridpoint b⟩)]
          simp
        · intro q _ hq
          by_cases hcond : (0, 0) ≤ a ∧ b ≤ q
          · rw [ite_eq_left hcond]
            dsimp only
            simp [hq]
          · rw [ite_eq_right hcond]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro p _ hp
        have hz : ∀ q : GridPoint,
            (if p = (0, 0) ∧ q = (1, 1) then (1 : ℤ) else 0) = 0 := by
          intro q
          rw [ite_eq_right]
          intro hconj
          exact hp hconj.1
        simp [hz]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hab, ite_eq_right hab]

-- ============ 理论的二参数结构：计数型总可分解 ============

/-
  【差异论落在判别线的可分解侧】

  v196–v197 建立了判别线：Möbius 非负 ⟺ 可分解。

  这一节回答"理论的参数关系落在哪一侧"：

  **差异论的二参数结构是"计数型"的**——两个参数分别作用于
  两个坐标（强度 × 维度/对位位），秩函数是"数点"。

  而点集型结构**总是**可分解：每个点贡献一个独立的矩形，
  没有 Casson–Zomorodian 那种"映射方向"的耦合。

  所以：**差异论的多参数结构落在可分解侧。**

  这不是坏消息，是好消息：
    · 意味着 barcode 在多参数下仍然存在（只要用对坐标）；
    · 意味着读数仍然完备，不会出现"无法离散表示"的病态；
    · 意味着理论的不可分解风险被排除了——它不是 Casson–Zomorodian 那种病。

  真正的不可分解需要"线性代数型"的耦合
  （v196 的 czRank 就是：映射到 (1,1) 是零映射而不是恒等）。
  那是"结构"层面的，不是"计数"层面的。
  差异论的读数是计数，所以它天然站在这一侧。
-/

-- 点集型秩：在阈值 b 之上、且 a ≤ b 时的点数。
def pointRank (M : GridPoint → ℤ) (a b : GridPoint) : ℤ :=
  if a ≤ b then ∑ p : GridPoint, (if b ≤ p then M p else 0) else 0

-- 【可分解】点集型二参数结构总是可分解（每个点一个矩形）。
theorem point_set_decomposable (M : GridPoint → ℤ) (hM : ∀ p, 0 ≤ M p) :
    ∃ c : GridPoint → GridPoint → ℤ,
      (∀ p q, 0 ≤ c p q) ∧
      (∀ a b, intervalRank c a b = pointRank M a b) := by
  refine ⟨fun p q => if p = (0, 0) then M q else 0, ?_, ?_⟩
  · intro p q
    dsimp only
    by_cases hp : p = (0, 0)
    · rw [ite_eq_left hp]
      exact hM q
    · rw [ite_eq_right hp]
  · intro a b
    unfold intervalRank pointRank
    by_cases hab : a ≤ b
    · rw [ite_eq_left hab, ite_eq_left hab]
      rw [Finset.sum_eq_single (0, 0)]
      · apply Finset.sum_congr rfl
        intro q _
        have h0a : (0, 0) ≤ a := Prod.mk_le_mk.mpr ⟨Fin.zero_le _, Fin.zero_le _⟩
        by_cases hbq : b ≤ q
        · rw [ite_eq_left ⟨h0a, hbq⟩, ite_eq_left hbq]
          simp
        · rw [ite_eq_right (fun hconj => hbq hconj.2), ite_eq_right hbq]
      · intro p _ hp
        have hz : ∀ q : GridPoint, (if p = (0, 0) then M q else 0) = 0 := by
          intro q
          rw [ite_eq_right hp]
        simp [hz]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hab, ite_eq_right hab]

-- ============ 玩具网络：暹界 = 可标记的不确定性 ============

/-
  【最小的一块：有限网络的不确定性是可标记的】

  v189 证明了三界读数 = 差异谱的层析。这里把它接到一个
  **最小的玩具网络**上，看"黑箱"变成了什么。

  玩具网络：一层线性（权重 + 偏置），输入 Fin n → ℚ，输出 Fin k → ℚ。
  它的"激活模式"是一个 StateQuant k——这就是网络的内部状态。

  两个输入 x、y 经过网络，得到两个内部状态。在阈值 δ 下，
  它们的差异分成生 / 暹 / 死三界。

  **暹界**就是"恰好压在阈值上的那个维度"——网络在这里"说不清"。
  这就是黑箱的**可标记形态**：

    · 黑箱不是"全黑"（浊界）——那只是差异太小；
    · 也不是"全白"（清界）——那只是差异很大；
    · 而是"知道这里有东西，但说不清是什么"（暹界）。

  `uncertainty_is_markable` 说：这个不确定性有三个性质——
  **有限、可枚举、守恒**。这三条合起来就是"可标记"。

  这不是工程推销。这是一个形式化的事实：
  在有限网络里，不确定性从来不是弥漫在连续统里的雾，
  而是**有限个点上的台阶**。
-/

-- 玩具网络：一层线性（权重 + 偏置）。
structure ToyNet (n k : ℕ) where
  W : Fin k → Fin n → ℚ
  b : Fin k → ℚ

-- 网络在输入上的激活模式（内部状态）。
def ToyNet.activations {n k : ℕ} (N : ToyNet n k) (x : Fin n → ℚ) : StateQuant k :=
  { val := fun j => ∑ i : Fin n, N.W j i * x i + N.b j, phase := .neutral }

-- 网络对两个输入在阈值 δ 下"不确定"：暹界非空。
def ToyNet.uncertain {n k : ℕ} (N : ToyNet n k) (x y : Fin n → ℚ) (δ : ℚ) : Prop :=
  0 < xianReading (N.activations x) (N.activations y) δ

-- 【核心】不确定 ⟺ 存在一个维度，激活差恰好等于 δ。
theorem ToyNet.uncertain_iff {n k : ℕ} (N : ToyNet n k) (x y : Fin n → ℚ) (δ : ℚ) :
    N.uncertain x y δ ↔
      ∃ j : Fin (min k k), |pairDiff (N.activations x) (N.activations y) j| = δ :=
  xianReading_pos_iff _ _ _

-- 【有限】不确定性有界：暹界大小 ≤ 输出维度数。
theorem ToyNet.uncertain_le {n k : ℕ} (N : ToyNet n k) (x y : Fin n → ℚ) (δ : ℚ) :
    xianReading (N.activations x) (N.activations y) δ ≤ min k k := by
  unfold xianReading xianSet
  have h := Finset.card_le_card
    (Finset.subset_univ (Finset.univ.filter
      (fun j : Fin (min k k) => |pairDiff (N.activations x) (N.activations y) j| = δ)))
  simpa using h

-- 【可枚举】不确定的阈值只可能是有限个：恰好是那些激活差。
theorem ToyNet.uncertain_thresholds_finite {n k : ℕ} (N : ToyNet n k)
    (x y : Fin n → ℚ) :
    ∃ T : Finset ℚ,
      ∀ δ : ℚ, N.uncertain x y δ → δ ∈ T := by
  refine ⟨Finset.univ.image
    (fun j : Fin (min k k) => |pairDiff (N.activations x) (N.activations y) j|), ?_⟩
  intro δ hδ
  rw [ToyNet.uncertain_iff] at hδ
  obtain ⟨j, hj⟩ := hδ
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩

-- 【确定】若 δ 避开所有激活差，则网络完全确定（暹界为空）。
theorem ToyNet.certain_of_avoiding {n k : ℕ} (N : ToyNet n k) (x y : Fin n → ℚ) (δ : ℚ)
    (h : ∀ j : Fin (min k k),
      |pairDiff (N.activations x) (N.activations y) j| ≠ δ) :
    xianReading (N.activations x) (N.activations y) δ = 0 := by
  by_contra hpos
  have hpos' : N.uncertain x y δ := Nat.pos_of_ne_zero hpos
  rw [ToyNet.uncertain_iff] at hpos'
  obtain ⟨j, hj⟩ := hpos'
  exact h j hj

-- 【守恒】三界守恒：清 + 暹 + 浊 = r，且"没有不确定" ⟺ 清 + 浊拉满。
theorem ToyNet.uncertainty_conservation {n k : ℕ} (N : ToyNet n k) (x y : Fin n → ℚ) (δ : ℚ) :
    sReading (N.activations x) (N.activations y) δ
        + xianReading (N.activations x) (N.activations y) δ
        + dReading (N.activations x) (N.activations y) δ
        = r_rel (N.activations x) (N.activations y) ∧
      (sReading (N.activations x) (N.activations y) δ
          + dReading (N.activations x) (N.activations y) δ
          = r_rel (N.activations x) (N.activations y)
        ↔ xianReading (N.activations x) (N.activations y) δ = 0) := by
  have h := qty_pair_conservation (N.activations x) (N.activations y) δ
  refine ⟨h, ?_⟩
  omega

-- 【可标记的不确定性】三条性质合起来：有限 + 可枚举 + 守恒。
theorem uncertainty_is_markable {n k : ℕ} (N : ToyNet n k) (x y : Fin n → ℚ) (δ : ℚ) :
    -- (1) 有限：不确定性有界
    (xianReading (N.activations x) (N.activations y) δ ≤ min k k) ∧
    -- (2) 可枚举：不确定 ⟺ 某个维度恰好卡在 δ 上
    (N.uncertain x y δ ↔
      ∃ j : Fin (min k k), |pairDiff (N.activations x) (N.activations y) j| = δ) ∧
    -- (3) 守恒：清 + 暹 + 浊 = r，"没有不确定" ⟺ 清 + 浊拉满
    (sReading (N.activations x) (N.activations y) δ
        + xianReading (N.activations x) (N.activations y) δ
        + dReading (N.activations x) (N.activations y) δ
        = r_rel (N.activations x) (N.activations y) ∧
      (sReading (N.activations x) (N.activations y) δ
          + dReading (N.activations x) (N.activations y) δ
          = r_rel (N.activations x) (N.activations y)
        ↔ xianReading (N.activations x) (N.activations y) δ = 0)) :=
  ⟨N.uncertain_le x y δ,
   N.uncertain_iff x y δ,
   N.uncertainty_conservation x y δ⟩

-- ============ 真实网络：层 = 相容族 = 可解释性判据 ============

/-
  【网络 = 层塔上的相容族；可解释性 = 相干性】

  仿 Grothendieck 时的那条线，这里接上：
  神经网络可以编码成 LayerLadder 上的一个族。

  编码：
    · 网络的第 i 层 → LayerLadder 的第 i 层（δ_i）；
    · 第 i 层的激活 → 一个 ResLayer.object ⟨δ_i⟩ n（凝结对象）；
    · 层间的"池化" → ResLayer.resolution（消解）。

  于是"网络状态"是一个 NetState（每层一个对象），
  而"相干"意味着：深层（粗层）是浅层（细层）的消解像。

  **核心判据**：
    网络可解释 ⟺ 它的层族是相干的 ⟺ 全局状态由输入层唯一决定。

  这不是理想化的口号——它是 v174 的 sheaf_topos_bridge：
  相容族（towerLimit）与最细层对象同构。

  而"不可解释"（黑箱）恰好是**不相干**：某一层的激活不是下层的消解像，
  于是它携带了输入层没有的信息——这正是 v194 的"一维投影不够"。

  所以"黑箱"有了一个精确的层论位置：
  **黑箱 = 一个不相干的层族 = 携带了超出消解的新信息。**
-/

-- 网络状态：每层一个激活对象。
def NetState (L : LayerLadder) (n : ℕ) : Type :=
  ∀ i : Fin L.m, ResLayer.object ⟨L.δ i⟩ n

-- 相干：深层（粗层）是浅层（细层）的消解像。
def Coherent (L : LayerLadder) (n : ℕ) (f : NetState L n) : Prop :=
  ∀ (i j : Fin L.m) (h : i ≤ j), ResLayer.resolution (L.le_delta h) (f j) = f i

-- 任意层 ≤ 最细层。
private theorem le_finest (L : LayerLadder) (hm : 0 < L.m) (i : Fin L.m) :
    i ≤ L.finest hm := by
  show i.val ≤ (L.finest hm).val
  have hf : (L.finest hm).val = L.m - 1 := rfl
  rw [hf]
  have := i.isLt
  omega

-- 【判据·充分】相干 ⟹ 全局状态由输入层（最细层）唯一决定。
theorem coherent_has_source (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    {f : NetState L n} (hf : Coherent L n f) :
    ∃ g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n,
      ∀ i, f i = ResLayer.resolution (L.le_delta (le_finest L hm i)) g :=
  ⟨f (L.finest hm), fun i => (hf i (L.finest hm) (le_finest L hm i)).symm⟩

-- 【判据·必要】若全局状态来自输入层，则它相干。
theorem source_implies_coherent (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    {f : NetState L n} {g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n}
    (hg : ∀ i, f i = ResLayer.resolution (L.le_delta (le_finest L hm i)) g) :
    Coherent L n f := by
  intro i j hij
  rw [hg j, hg i, ResLayer.resolution_comp]

-- 【可解释性判据】网络可解释 ⟺ 相干 ⟺ 由输入层唯一决定。
theorem interpretability_criterion (L : LayerLadder) (hm : 0 < L.m) (n : ℕ) :
    (∀ f : NetState L n, Coherent L n f ↔
      ∃ g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n,
        ∀ i, f i = ResLayer.resolution (L.le_delta (le_finest L hm i)) g) ∧
    Nonempty (towerLimit L n ≃ ResLayer.object ⟨L.δ (L.finest hm)⟩ n) :=
  ⟨fun f => ⟨fun hf => coherent_has_source L hm (f := f) hf,
             fun ⟨_g, hg⟩ => source_implies_coherent L hm (f := f) hg⟩,
   sheaf_topos_bridge L hm n⟩

-- ============ 非线性 = 打破相干性 ============

/-
  【ReLU 是相干的破坏者：表达力的来源】

  v200 说：网络可解释 ⟺ 层族相干 ⟺ 深层是浅层的消解像。
  这里给出"非线性打破相干性"的最小定理。

  相干性（信息不丢失）：如果深层的两个状态相同，
  那么浅层的对应状态必须"足够近"（commonDist ≤ δ）。

  ReLU（x ↦ max 0 x）恰好违反它：
  两个很远的负数（-1 和 -2）经过 ReLU 后都是 0——深层相同，
  但浅层距离是 1 > 0。

  这就是"非线性 = 表达力"的来源：
  ReLU 把"不同的东西"映射到"相同的东西"，创造了新的等价关系，
  而这些等价关系不是"按距离凝结"来的——它们是"按符号截断"来的。

  所以：
    · 池化（按距离凝结）是相干的 —— 它是消解；
    · ReLU（按符号截断）是不相干的 —— 它创造了新的信息结构。

  这把 v200 的判据精确化：
  **黑箱 = 非相干映射 = 不按距离凝结的映射。**
  而"表达能力"就是它偏离相干性的程度——
  偏离越多，能表达的东西越多，能还原的东西越少。
-/

-- ReLU。
def relu (q : ℚ) : ℚ := max 0 q

-- ReLU 作用于状态（逐分量）。
def reluState {n : ℕ} (x : StateQuant n) : StateQuant n :=
  { val := fun i => relu (x.val i), phase := x.phase }

-- 相干映射：深层的相同 ⟹ 浅层的足够近。
def CoherentMap {n m : ℕ} (δ : ℚ) (f : StateQuant n → StateQuant m) : Prop :=
  ∀ x y, f x = f y → commonDist x y ≤ δ

-- 【非线性破坏相干性】ReLU 不相干：存在两个"远"的状态被映到同一个"近"。
theorem relu_breaks_coherence :
    ∃ (x y : StateQuant 1) (δ : ℚ),
      reluState x = reluState y ∧ δ < commonDist x y := by
  refine ⟨{ val := fun _ => -1, phase := .neutral },
          { val := fun _ => -2, phase := .neutral }, 0, ?_, ?_⟩
  · -- reluState x = reluState y（都是 0 向量）
    have hv : (fun _ : Fin 1 => relu (-1 : ℚ)) = (fun _ : Fin 1 => relu (-2 : ℚ)) := by
      funext i
      norm_num [relu]
    show reluState ({ val := fun _ => (-1 : ℚ), phase := .neutral } : StateQuant 1)
       = reluState ({ val := fun _ => (-2 : ℚ), phase := .neutral } : StateQuant 1)
    simp only [reluState]
    rw [hv]
  · -- 0 < commonDist（-1 与 -2 的距离是 1）
    rw [commonDist_eq_sum_sq]
    simp only [pairDiff]
    norm_num

-- 【对照】恒等映射相干：它能还原一切。
theorem id_coherent {n : ℕ} (δ : ℚ) (hδ : 0 ≤ δ) :
    CoherentMap δ (id : StateQuant n → StateQuant n) := by
  intro x y h
  have hxy : x = y := h
  rw [hxy]
  have h0 : commonDist y y = 0 := by
    rw [commonDist_eq_sum_sq]
    apply Finset.sum_eq_zero
    intro i _
    have heq : Fin.embedLeft i = Fin.embedRight i := Fin.ext rfl
    simp only [pairDiff]
    rw [heq, sub_self]
    norm_num
  rw [h0]
  exact hδ

-- 【表达力 = 打破相干性】恒等相干，ReLU 不相干。
theorem expression_breaks_coherence :
    (∀ {n : ℕ} (δ : ℚ), 0 ≤ δ →
      CoherentMap δ (id : StateQuant n → StateQuant n)) ∧
    (∃ (x y : StateQuant 1) (δ : ℚ),
      reluState x = reluState y ∧ δ < commonDist x y) :=
  ⟨fun δ hδ => id_coherent δ hδ, relu_breaks_coherence⟩

-- 【破坏无界】ReLU 对任何阈值都不相干：它的破坏是彻底的。
theorem relu_gap_unbounded (δ : ℚ) :
    ¬ CoherentMap δ (reluState : StateQuant 1 → StateQuant 1) := by
  intro h
  let N : ℚ := |δ| + 1
  have hN : (0 : ℚ) < N := by
    have := abs_nonneg δ
    unfold N; linarith
  have hreluN : relu (-N) = 0 := by
    unfold relu
    rw [max_eq_left (by linarith : -N ≤ 0)]
  have hrelu0 : relu (0 : ℚ) = 0 := by
    unfold relu
    rw [max_eq_left le_rfl]
  have hx : reluState ({ val := fun _ => -N, phase := .neutral } : StateQuant 1)
          = reluState ({ val := fun _ => (0 : ℚ), phase := .neutral } : StateQuant 1) := by
    have hv : (fun _ : Fin 1 => relu (-N)) = (fun _ : Fin 1 => relu (0 : ℚ)) := by
      funext i; rw [hreluN, hrelu0]
    show reluState ({ val := fun _ => -N, phase := .neutral } : StateQuant 1)
       = reluState ({ val := fun _ => (0 : ℚ), phase := .neutral } : StateQuant 1)
    simp only [reluState]
    rw [hv]
  have hcd : δ < commonDist ({ val := fun _ => -N, phase := .neutral } : StateQuant 1)
                              ({ val := fun _ => (0 : ℚ), phase := .neutral } : StateQuant 1) := by
    rw [commonDist_eq_sum_sq]
    simp only [pairDiff]
    have hval : (∑ i : Fin (min 1 1),
        (((fun _ : Fin 1 => -N) (Fin.embedLeft i)
          - (fun _ : Fin 1 => (0 : ℚ)) (Fin.embedRight i)) ^ 2)) = N ^ 2 := by
      simp
    rw [hval]
    unfold N
    nlinarith [abs_nonneg δ, sq_abs δ, sq_nonneg (δ - 1 / 2)]
  exact absurd (h _ _ hx) (not_le.mpr hcd)

-- 【可解释性的刻度】id 在最左（gap 0），ReLU 在最右（gap ∞）。
theorem interpretability_scale :
    (∀ {n : ℕ} (δ : ℚ), 0 ≤ δ →
      CoherentMap δ (id : StateQuant n → StateQuant n)) ∧
    (∀ δ : ℚ, ¬ CoherentMap δ (reluState : StateQuant 1 → StateQuant 1)) :=
  ⟨fun δ hδ => id_coherent δ hδ, relu_gap_unbounded⟩

-- ============ CNN 的不相干不可修复 ============

/-
  【黑箱一旦产生，就无法被后续层修复】

  CNN 的两种基本操作：
    · 池化（pooling）：按距离凝结 —— 相干层；
    · ReLU：按符号截断 —— 不相干切口。

  编码成函数的复合：CNN = 池化 + ReLU 的交替。

  核心定理（gap_compose_left）：
  **如果某一层不相干，那么它的任何后续复合都不相干。**

  即：ReLU 引入的 gap 永远不会被后面的池化或线性的层"修复"。
  这是一个坏消息，也是一个精确的结构事实：
  **黑箱的深度是单调的**——一旦某个位置切断了相干性，
  网络之后的所有层都在那个切口之上。

  这不是缺陷，是深度的定义：
  **深度 = 切口数；可解释性 = 切口之间剩下的相干。**

  CNN 的典型结构恰好是"相干 - 切口 - 相干 - 切口"的锯齿：
  卷积（线性，相干）+ 池化（凝结，相干）+ ReLU（切口）+ ...
  每一次 ReLU 都在锯齿上留下一个永久的缺口。
-/

-- 【坏消息】不相干在左复合下保持：黑箱一旦产生就无法修复。
theorem gap_compose_left {n m l : ℕ} (f : StateQuant n → StateQuant m)
    (g : StateQuant m → StateQuant l) (δ : ℚ) (hf : ¬ CoherentMap δ f) :
    ¬ CoherentMap δ (fun x => g (f x)) := by
  intro hg
  unfold CoherentMap at hf
  push Not at hf
  obtain ⟨x, y, hxy, hcd⟩ := hf
  have hcomp : g (f x) = g (f y) := by rw [hxy]
  exact absurd (hg x y hcomp) (not_le.mpr hcd)

-- 【黑箱单调】不相干不可修复 + 恒等相干。
theorem cnn_gap_persists :
    (∀ {n m l : ℕ} (f : StateQuant n → StateQuant m)
        (g : StateQuant m → StateQuant l) (δ : ℚ),
      ¬ CoherentMap δ f → ¬ CoherentMap δ (fun x => g (f x))) ∧
    (∀ {n : ℕ} (δ : ℚ), 0 ≤ δ →
      CoherentMap δ (id : StateQuant n → StateQuant n)) :=
  ⟨fun f g δ hf => gap_compose_left f g δ hf,
   fun δ hδ => id_coherent δ hδ⟩

-- ============ 可解释性 = 可编码性 ============

/-
  【两条线合流：可解释 ⟺ 可编码】

  v200–v203 说的是：网络可解释 ⟺ 层族相干；黑箱 = 不相干 = 无法修复。

  但"相干"一直是个否定式的说法：深层不能携带超出消解的新信息。
  这里换成**肯定式**：

      可解释 ⟺ 存在编码

  具体地：一个网络态 f 若相干，就完全由**一个**源对象决定——
  把这唯一的源沿塔逐层消解，就重建出整条链。这个源就是 f 的代码。

      (encode)  源 → 层族    （解码：沿塔消解）
      (decode)  层族 → 源    （取最细层）

  三条：
  (1) 编码总是相干的——解码必然合法；
  (2) 解码再编码 = 恒等——代码唯一；
  (3) 相干 ⟺ 落在编码的像里——**可解释就是可编码**。

  于是"黑箱"有了一个肯定式的解释：**黑箱 = 没有代码。**
  不是"我们看不懂它"，是"它根本不能被一个单源生成"。

  这和 v214–v215 的结论接上了：符号能编码，是因为它有限、可判定。
  网络能编码，是因为它相干。两层意思其实是同一句：

      **能被写下来的东西，才谈得上被理解。**
-/

-- 一层对象在恒等消解下不动（对任意 ≤ 的证明成立）。
theorem resolution_self {δ : ℚ} (h : δ ≤ δ) {n : ℕ} (q : ResLayer.object ⟨δ⟩ n) :
    ResLayer.resolution h q = q := by
  rw [show h = le_refl δ from Subsingleton.elim h _]
  exact resolution_refl q

-- 编码：把唯一的源沿塔消解，重建整条层族。
def encode (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    (g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n) : NetState L n :=
  fun i => ResLayer.resolution (L.le_delta (le_finest L hm i)) g

-- 解码：取最细层的那个对象。
def decode (L : LayerLadder) (hm : 0 < L.m) {n : ℕ} (f : NetState L n) :
    ResLayer.object ⟨L.δ (L.finest hm)⟩ n :=
  f (L.finest hm)

-- (1) 编码总是相干的：解码必然合法。
theorem encode_coherent (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    (g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n) : Coherent L n (encode L hm g) :=
  source_implies_coherent L hm (f := encode L hm g) (g := g) (fun _ => rfl)

-- (2a) 解码再编码 = 恒等：代码唯一。
theorem decode_encode (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    (g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n) :
    decode L hm (encode L hm g) = g := by
  show ResLayer.resolution (L.le_delta (le_finest L hm (L.finest hm))) g = g
  exact resolution_self _ g

-- (2b) 编码再解码 = 恒等（相干时）。
theorem encode_decode (L : LayerLadder) (hm : 0 < L.m) {n : ℕ} {f : NetState L n}
    (hf : Coherent L n f) : encode L hm (decode L hm f) = f := by
  obtain ⟨g, hg⟩ := coherent_has_source L hm hf
  have hself : ResLayer.resolution
      (L.le_delta (le_finest L hm (L.finest hm))) g = g :=
    resolution_self _ g
  funext i
  show ResLayer.resolution (L.le_delta (le_finest L hm i)) (f (L.finest hm)) = f i
  rw [hg (L.finest hm), hself, hg i]

-- 编码是单射：不同的源给不同的层族。
theorem encode_injective (L : LayerLadder) (hm : 0 < L.m) {n : ℕ} :
    Function.Injective (encode L hm (n := n)) := by
  intro g g' h
  have h' := congrFun h (L.finest hm)
  rw [show encode L hm g (L.finest hm) = g from decode_encode L hm g,
      show encode L hm g' (L.finest hm) = g' from decode_encode L hm g'] at h'
  exact h'

-- (3) 【可解释 = 可编码】网络态相干 ⟺ 它是某个源的编码。
theorem interpretability_is_encodability (L : LayerLadder) (hm : 0 < L.m) (n : ℕ) :
    -- 相干 ⟺ 落在编码的像里
    (∀ f : NetState L n, Coherent L n f ↔ ∃ g, f = encode L hm g) ∧
    -- 编码总是相干的
    (∀ g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n, Coherent L n (encode L hm g)) ∧
    -- 编码单射（源唯一）
    Function.Injective (encode L hm (n := n)) ∧
    -- 编解码互逆
    (∀ g : ResLayer.object ⟨L.δ (L.finest hm)⟩ n, decode L hm (encode L hm g) = g) ∧
    (∀ f : NetState L n, Coherent L n f → encode L hm (decode L hm f) = f) :=
  ⟨fun f => ⟨fun hf => ⟨decode L hm f, (encode_decode L hm hf).symm⟩,
             fun ⟨g, hg⟩ => hg ▸ encode_coherent L hm g⟩,
   fun g => encode_coherent L hm g,
   encode_injective L hm,
   fun g => decode_encode L hm g,
   fun _ hf => encode_decode L hm hf⟩

-- 【黑箱 = 没有代码】不相干 ⟹ 不存在能生成它的源。
theorem incoherent_not_encodable (L : LayerLadder) (hm : 0 < L.m) {n : ℕ}
    {f : NetState L n} (h : ¬ Coherent L n f) :
    ¬ ∃ g, f = encode L hm g := by
  rintro ⟨g, rfl⟩
  exact h (encode_coherent L hm g)

-- 【两条线合流】层论侧（可解释 ⟺ 有单源）+ 映射侧（id 可解释 / relu 不可解释 / 黑箱不可修复）。
theorem explainability_meets_encodability :
    -- 网络可解释 ⟺ 存在单源编码
    (∀ (L : LayerLadder) (hm : 0 < L.m) (n : ℕ) (f : NetState L n),
      Coherent L n f ↔ ∃ g, f = encode L hm g) ∧
    -- id 相干（可编码，gap = 0）
    (∀ {n : ℕ} (δ : ℚ), 0 ≤ δ → CoherentMap δ (id : StateQuant n → StateQuant n)) ∧
    -- ReLU 不相干（不可编码，gap = ∞）
    (∀ δ : ℚ, ¬ CoherentMap δ (reluState : StateQuant 1 → StateQuant 1)) ∧
    -- 黑箱不可修复（不相干在左复合下保持）
    (∀ {n m l : ℕ} (f : StateQuant n → StateQuant m)
        (g : StateQuant m → StateQuant l) (δ : ℚ),
      ¬ CoherentMap δ f → ¬ CoherentMap δ (fun x => g (f x))) :=
  ⟨fun L hm n f => (interpretability_is_encodability L hm n).1 f,
   fun δ hδ => id_coherent δ hδ,
   fun δ => relu_gap_unbounded δ,
   fun f g δ hf => gap_compose_left f g δ hf⟩

-- ============ 二参数层格的第一贝蒂数 ============

/-
  【第一贝蒂数：观察层塔 vs 计算网格】

  外部对照（arXiv 2610.17117, NeurIPS 2026）原文：

    "A single-layer matching graph has no cycles, so algebraic H¹ = 0...
     Stacking the same activations across layers gives a grid with
     b₁ = N(L−1) squares, and each square asks whether the layer-l-to-layer-l+1
     transformation commutes with paraphrase equivalence."

  读清楚三件事：
  · N 是**改述对（边）**的数量；改述图是**树**（所以他们单层 H¹ = 0）；
  · b₁ = N(L−1) 是"改述对 × 层转移"的方格数；
  · **每个方格问的是：层变换 T_l 是否与改述等价交换。**

  这和我们的层塔**不是同一个结构**：

  | | 他们的网格 | 我们的观察层塔 |
  | --- | --- | --- |
  | 底空间 | 改述对 × 层转移 | 观察分辨率 |
  | 方格问什么 | 层变换是否与改述交换 | 消解是否函子 |
  | 自动吗 | **否**——这就是诊断 | **是**——`resolution_comp` |
  | b₁ | N(L−1) > 0 | **0** |

  在我们的层塔上，每个方格都被 `resolution_comp` 填上，
  所以第一贝蒂数恒为 0。这不是巧合，是 `observation_always_coherent`
  （v220）的几何形式：**任何映射按层塔观测都相干**，
  所以观察层塔**不携带任何诊断信息**。

  因此正确的结论不是"我们能解释他们的 b₁"，而是：

      **sheaf 诊断必须建在计算图上，不能建在观察层塔上。**
      在后者上一切自动相干，诊断是空的。

  下面的 Euler 恒等式**只是组合算术**，与他们的网格没有结构对应；
  `b1_grid_degree_identity` 这个名字就是在提醒这一点。
-/

-- 组合版第一贝蒂数：b₁ = 1 − V + E − F（b₂ = 0，连通）。用 ℤ，公式对一切整数成立。
def eulerB1 (V E F : ℤ) : ℤ := 1 - V + E - F

-- 【层塔填满每个方格】三层 i ≤ j ≤ k，两条路径给出同一个结果。
-- 这是**观察**的函子性（`resolution_comp`），不是他们方格里的"层变换交换"。
theorem layer_square_commutes (L : LayerLadder) {n : ℕ} (i j k : Fin L.m)
    (h₁ : i ≤ j) (h₂ : j ≤ k) (q : ResLayer.object ⟨L.δ k⟩ n) :
    ResLayer.resolution (L.le_delta h₁) (ResLayer.resolution (L.le_delta h₂) q) =
      ResLayer.resolution (L.le_delta (h₁.trans h₂)) q :=
  ResLayer.resolution_comp (L.le_delta h₂) (L.le_delta h₁) q

-- 【全填 ⟹ b₁ = 0】n×n 观察层塔，所有面都填上。
theorem euler_b1_full (n : ℤ) :
    eulerB1 (n * n) (2 * n * (n - 1)) ((n - 1) * (n - 1)) = 0 := by
  unfold eulerB1
  ring

-- 【骨架 ⟹ b₁ = (n−1)²】一个面都不填。
theorem euler_b1_skeleton (n : ℤ) :
    eulerB1 (n * n) (2 * n * (n - 1)) 0 = (n - 1) * (n - 1) := by
  unfold eulerB1
  ring

-- 【每切一刀吃掉一个面】b₁ = 未填的面数 = 切口数。
theorem euler_b1_cuts (n cuts : ℤ) :
    eulerB1 (n * n) (2 * n * (n - 1)) ((n - 1) * (n - 1) - cuts) = cuts := by
  unfold eulerB1
  ring

-- 【N×L 网格骨架】无 2-胞腔的组合网格。
theorem euler_b1_grid_skeleton (N L : ℤ) :
    eulerB1 (N * L) (N * (L - 1) + L * (N - 1)) 0 = (N - 1) * (L - 1) := by
  unfold eulerB1
  ring

-- 【组合恒等式】注意：这是**纯算术**，与 2610.17117 的网格没有结构对应。
-- 保留它只是为了记录那个偶然相等的算式，不构成任何解释。
theorem b1_grid_degree_identity (N L : ℤ) :
    (N - 1) * (L - 1) + (L - 1) = N * (L - 1) := by
  ring

-- 【对照：两种看法】观察层塔恒相干（b₁ = 0）；诊断必须建在计算图上。
theorem two_views_of_b1 :
    -- (1) 观察层塔：每个方格交换（消解是函子的像）
    (∀ (L : LayerLadder) {n : ℕ} (i j k : Fin L.m) (h₁ : i ≤ j) (h₂ : j ≤ k)
        (q : ResLayer.object ⟨L.δ k⟩ n),
      ResLayer.resolution (L.le_delta h₁) (ResLayer.resolution (L.le_delta h₂) q) =
        ResLayer.resolution (L.le_delta (h₁.trans h₂)) q) ∧
    -- (2) 全填 ⟹ b₁ = 0（观察层塔）
    (∀ n : ℤ, eulerB1 (n * n) (2 * n * (n - 1)) ((n - 1) * (n - 1)) = 0) ∧
    -- (3) 骨架 ⟹ b₁ = (n−1)²（无一格填）
    (∀ n : ℤ, eulerB1 (n * n) (2 * n * (n - 1)) 0 = (n - 1) * (n - 1)) ∧
    -- (4) 每切一刀 b₁ 加一（= 切口数 = 深度）
    (∀ n cuts : ℤ, eulerB1 (n * n) (2 * n * (n - 1)) ((n - 1) * (n - 1) - cuts) = cuts) ∧
    -- (5) N×L 网格骨架 ⟹ b₁ = (N−1)(L−1)
    (∀ N L : ℤ, eulerB1 (N * L) (N * (L - 1) + L * (N - 1)) 0 = (N - 1) * (L - 1)) :=
  ⟨fun L _ _ _ _ h₁ h₂ q => layer_square_commutes L _ _ _ h₁ h₂ q,
   fun n => euler_b1_full n,
   fun n => euler_b1_skeleton n,
   fun n cuts => euler_b1_cuts n cuts,
   fun N L => euler_b1_grid_skeleton N L⟩

-- ============ 精确 gap：一个具体的网络 ============

/-
  【gap 到底是什么数？】

  v202 说 gap ∈ [0, ∞]：id 在 0，ReLU 在 ∞。
  但 ReLU 之所以是 ∞，是因为定义域是整个 ℚ（无界）——
  推得越远，坍缩的跨度越大，所以任何 δ 都不够。

  在**有界的输入域**上，ReLU 的 gap 是一个具体的有限数。

  取最简的具体网络：

      f(x) = max 0 (a·x − c),   x ∈ [−1, 1],   a > 0, 0 ≤ c ≤ a

  坍缩集 = {x : a·x − c ≤ 0} = {x ≤ c/a}（a > 0）。
  所以最远的一对被压在一起：x = −1 与 y = c/a。

      距离 = (c/a − (−1))² = (c/a + 1)²

  于是

      **gap(f) = (c/a + 1)²**

  两个端点：

    · c = 0（标准 ReLU max 0 (a x)）：gap = 1
    · c = a（ReLU 杀死整个盒子）：gap = 4

  而且 gap 关于 c/a 单调递增。

  这就是"gap 的精确值"：不是区间 [0,∞] 里的一个模糊位置，
  是一个可以写下来的数——而且它只依赖 **bias / weight 之比**。
-/

-- 具体网络：x ↦ max 0 (a x − c)。
def reluAffine (a c x : ℚ) : ℚ := max 0 (a * x - c)

-- 一维 commonDist 就是平方差（把 StateQuant 与 ℚ 接上）。
theorem commonDist_one (x y : StateQuant 1) :
    commonDist x y = (x.val 0 - y.val 0) ^ 2 := by
  have hsub : ∀ p q : Fin (min 1 1), p = q := fun p q =>
    Fin.ext (by
      have h1 : min 1 1 ≤ 1 := Nat.min_le_left 1 1
      have hp := p.isLt
      have hq := q.isLt
      omega)
  have h1 : x.val (Fin.embedLeft (⟨0, by omega⟩ : Fin (min 1 1))) = x.val 0 :=
    congrArg x.val (hsub _ _)
  have h2 : y.val (Fin.embedRight (⟨0, by omega⟩ : Fin (min 1 1))) = y.val 0 :=
    congrArg y.val (hsub _ _)
  unfold commonDist commonDim
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (min 1 1))]
  · rw [h1, h2]
  · intro c _ hc
    exact absurd (hsub c _) hc
  · intro hc
    exact absurd (Finset.mem_univ _) hc

-- 【gap 的上界】[−1,1] 上任何坍缩的距离都 ≤ (c/a + 1)²。
theorem reluAffine_gap_upper (a c : ℚ) (ha : 0 < a) (_hc0 : 0 ≤ c) (_hc : c ≤ a)
    (x y : ℚ) (hx1 : -1 ≤ x) (_hx2 : x ≤ 1) (hy1 : -1 ≤ y) (_hy2 : y ≤ 1)
    (h : reluAffine a c x = reluAffine a c y) :
    (x - y) ^ 2 ≤ (c / a + 1) ^ 2 := by
  by_cases hx : 0 < a * x - c
  · have hxm : max 0 (a * x - c) = a * x - c := max_eq_right (le_of_lt hx)
    by_cases hy : 0 < a * y - c
    · have hym : max 0 (a * y - c) = a * y - c := max_eq_right (le_of_lt hy)
      unfold reluAffine at h
      rw [hxm, hym] at h
      have hxy : x = y := mul_left_cancel₀ (ne_of_gt ha) (by linarith)
      have hz : (y - y) ^ 2 = 0 := by ring
      rw [hxy, hz]
      exact sq_nonneg _
    · have hym : max 0 (a * y - c) = 0 := max_eq_left (not_lt.mp hy)
      unfold reluAffine at h
      rw [hxm, hym] at h
      linarith
  · have hx' : a * x - c ≤ 0 := not_lt.mp hx
    have hxm : max 0 (a * x - c) = 0 := max_eq_left hx'
    unfold reluAffine at h
    rw [hxm] at h
    have hy' : a * y - c ≤ 0 := by
      by_contra hcon
      have hcon' : 0 < a * y - c := not_le.mp hcon
      have hym : max 0 (a * y - c) = a * y - c := max_eq_right (le_of_lt hcon')
      rw [hym] at h
      linarith
    have hxb : x ≤ c / a := by
      rw [le_div_iff₀ ha]
      linarith
    have hyb : y ≤ c / a := by
      rw [le_div_iff₀ ha]
      linarith
    have hlo : -(c / a + 1) ≤ x - y := by linarith
    have hhi : x - y ≤ c / a + 1 := by linarith
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ c / a + 1 - (x - y))
                          (by linarith : (0:ℚ) ≤ c / a + 1 + (x - y))]

-- 【gap 的见证】x = −1 与 y = c/a 被压成同一个值，距离正好是 (c/a + 1)²。
theorem reluAffine_gap_witness (a c : ℚ) (ha : 0 < a) (hc0 : 0 ≤ c) (hc : c ≤ a) :
    -1 ≤ (-1 : ℚ) ∧ (-1 : ℚ) ≤ 1 ∧ -1 ≤ c / a ∧ c / a ≤ 1 ∧
    reluAffine a c (-1) = reluAffine a c (c / a) ∧
    (-1 - c / a) ^ 2 = (c / a + 1) ^ 2 := by
  have hca0 : 0 ≤ c / a := div_nonneg hc0 (le_of_lt ha)
  have hca1 : c / a ≤ 1 := by
    rw [div_le_iff₀ ha]
    linarith
  refine ⟨by norm_num, by norm_num, by linarith, hca1, ?_, ?_⟩
  · unfold reluAffine
    have h1 : max 0 (a * (-1) - c) = 0 := by
      apply max_eq_left
      nlinarith
    have h2 : max 0 (a * (c / a) - c) = 0 := by
      apply max_eq_left
      rw [mul_div_cancel₀ c (ne_of_gt ha)]
      linarith
    rw [h1, h2]
  · ring

-- 【gap 的精确值】上界 + 见证 ⟹ gap 恰好是 (c/a + 1)²。
theorem reluAffine_gap_exact (a c : ℚ) (ha : 0 < a) (hc0 : 0 ≤ c) (hc : c ≤ a) :
    (∀ x y : ℚ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 →
      reluAffine a c x = reluAffine a c y → (x - y) ^ 2 ≤ (c / a + 1) ^ 2) ∧
    (∃ x y : ℚ, -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧
      reluAffine a c x = reluAffine a c y ∧ (x - y) ^ 2 = (c / a + 1) ^ 2) :=
  ⟨fun x y hx1 hx2 hy1 hy2 h => reluAffine_gap_upper a c ha hc0 hc x y hx1 hx2 hy1 hy2 h,
   ⟨-1, c / a,
    (reluAffine_gap_witness a c ha hc0 hc).1,
    (reluAffine_gap_witness a c ha hc0 hc).2.1,
    (reluAffine_gap_witness a c ha hc0 hc).2.2.1,
    (reluAffine_gap_witness a c ha hc0 hc).2.2.2.1,
    (reluAffine_gap_witness a c ha hc0 hc).2.2.2.2.1,
    (reluAffine_gap_witness a c ha hc0 hc).2.2.2.2.2⟩⟩

-- 【两个端点】标准 ReLU 的 gap = 1；杀死整个盒子时 gap = 4。
theorem reluAffine_gap_endpoints (a : ℚ) (ha : 0 < a) :
    (0 / a + 1) ^ 2 = 1 ∧ (a / a + 1) ^ 2 = 4 := by
  constructor
  · norm_num
  · rw [div_self (ne_of_gt ha)]
    norm_num

-- 【gap 单调】c/a 越大（ReLU 越偏），gap 越大。
theorem reluAffine_gap_monotone (a c₁ c₂ : ℚ) (ha : 0 < a)
    (h1 : 0 ≤ c₁) (h12 : c₁ ≤ c₂) (_h2 : c₂ ≤ a) :
    (c₁ / a + 1) ^ 2 ≤ (c₂ / a + 1) ^ 2 := by
  have hle : c₁ / a ≤ c₂ / a := div_le_div_of_nonneg_right h12 (le_of_lt ha)
  have hp1 : (0 : ℚ) ≤ c₁ / a + 1 := by
    have : 0 ≤ c₁ / a := div_nonneg h1 (le_of_lt ha); linarith
  have hp2 : (0 : ℚ) ≤ c₂ / a + 1 := by
    have : 0 ≤ c₂ / a := div_nonneg (le_trans h1 h12) (le_of_lt ha); linarith
  nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ c₂ / a + 1 - (c₁ / a + 1))
                        (by linarith : (0:ℚ) ≤ c₂ / a + 1 + (c₁ / a + 1))]

-- 【打包】有界域上 ReLU 的 gap 有精确闭式：随 bias/weight 比单调增长，取值恰在 [1,4]。
theorem gap_exact_value :
    -- (1) 精确值：(c/a + 1)²，且是紧的
    (∀ a c : ℚ, 0 < a → 0 ≤ c → c ≤ a →
      (∀ x y : ℚ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 →
        reluAffine a c x = reluAffine a c y → (x - y) ^ 2 ≤ (c / a + 1) ^ 2) ∧
      (∃ x y : ℚ, -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧
        reluAffine a c x = reluAffine a c y ∧ (x - y) ^ 2 = (c / a + 1) ^ 2)) ∧
    -- (2) 两端：对称 ReLU 得 1，全杀得 4
    (∀ a : ℚ, 0 < a → (0 / a + 1) ^ 2 = 1 ∧ (a / a + 1) ^ 2 = 4) ∧
    -- (3) 单调
    (∀ a c₁ c₂ : ℚ, 0 < a → 0 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ a →
      (c₁ / a + 1) ^ 2 ≤ (c₂ / a + 1) ^ 2) ∧
    -- (4) 接回 v202：gap 恒 ≥ 1，从不落入 (0,1)
    (∀ a c : ℚ, 0 < a → 0 ≤ c → c ≤ a → (1 : ℚ) ≤ (c / a + 1) ^ 2) :=
  ⟨fun a c ha hc0 hc => reluAffine_gap_exact a c ha hc0 hc,
   fun a ha => reluAffine_gap_endpoints a ha,
   fun a c₁ c₂ ha h1 h12 h2 => reluAffine_gap_monotone a c₁ c₂ ha h1 h12 h2,
   fun a c ha hc0 hc => by
     have hca0 : 0 ≤ c / a := div_nonneg hc0 (le_of_lt ha)
     nlinarith [mul_nonneg hca0 (by linarith : (0:ℚ) ≤ c / a + 2)]⟩

-- ============ 定义 6.1 与 6.2 的形式化：CoherentOnBox 与 IsGap ============

/-
  【论文 §6.2 的两个定义，在这里落地】

  在此之前，§6 的全部定理都把 "-1 ≤ x → x ≤ 1 → …" 内联在条件里——
  **但 §6.2 声称定义了两个东西**，而它们在 Lean 里并不存在。
  这是一个正规性缺口：论文说的"定义 6.1""定义 6.2"没有形式化对应物。

  现在补上：

  · `CoherentOnBox B δ f`：v201 的 `CoherentMap` 限制在盒 [−B, B] 上；
  · `IsGap B f g`：g 是 f 在盒 B 上的 gap（相干，且最小）。

  为什么用关系而不是函数？因为 ℚ 没有良序，"最小的 δ"不能写成
  `sInf`。把"g 是 gap"写成关系，既精确又构造。

  于是"gap = (c/a+1)²"被精确陈述为：

      IsGap 1 (reluAffine a c) ((c/a+1)²)

  由「上界」（定理 6.3）与「达到」（定理 6.4）两条合起来证。
-/

-- 盒上的相干：不把盒内的等值对推成更远。
def CoherentOnBox (B : ℚ) (δ : ℚ) (f : ℚ → ℚ) : Prop :=
  ∀ x y : ℚ, |x| ≤ B → |y| ≤ B → f x = f y → (x - y) ^ 2 ≤ δ

-- g 是 f 在盒 B 上的 gap：相干，且最小。
def IsGap (B : ℚ) (f : ℚ → ℚ) (g : ℚ) : Prop :=
  CoherentOnBox B g f ∧ ∀ δ : ℚ, CoherentOnBox B δ f → g ≤ δ

-- 【定理 6.5 的精确形式】gap = (c/a + 1)²。
theorem reluAffine_isGap (a c : ℚ) (ha : 0 < a) (hc0 : 0 ≤ c) (hc : c ≤ a) :
    IsGap 1 (reluAffine a c) ((c / a + 1) ^ 2) := by
  obtain ⟨hupper, hwit⟩ := reluAffine_gap_exact a c ha hc0 hc
  constructor
  · intro x y hx hy hxy
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    exact hupper x y hx1 hx2 hy1 hy2 hxy
  · intro δ hδ
    obtain ⟨x, y, hx1, hx2, hy1, hy2, hxy, hdist⟩ := hwit
    have hx : |x| ≤ 1 := abs_le.mpr ⟨hx1, hx2⟩
    have hy : |y| ≤ 1 := abs_le.mpr ⟨hy1, hy2⟩
    have hle := hδ x y hx hy hxy
    rw [hdist] at hle
    exact hle

-- 【定理 6.6 的精确形式】标准 ReLU（c = 0）的 gap 恰为 1。
theorem reluAffine_isGap_zero (a : ℚ) (ha : 0 < a) :
    IsGap 1 (reluAffine a 0) 1 := by
  have h := reluAffine_isGap a 0 ha le_rfl (le_of_lt ha)
  rwa [zero_div, zero_add, one_pow] at h

-- 【定理 6.6 的另一端】c = a 时 gap 恰为 4。
theorem reluAffine_isGap_full (a : ℚ) (ha : 0 < a) :
    IsGap 1 (reluAffine a a) 4 := by
  have h := reluAffine_isGap a a ha (le_of_lt ha) le_rfl
  rw [div_self (ne_of_gt ha)] at h
  norm_num at h
  exact h

-- 【打包】两个定义 + gap 的精确值（含两端）。
theorem gap_definition_formalized :
    -- (1) 定义 6.1
    (∀ (B δ : ℚ) (f : ℚ → ℚ),
      CoherentOnBox B δ f ↔
        ∀ x y : ℚ, |x| ≤ B → |y| ≤ B → f x = f y → (x - y) ^ 2 ≤ δ) ∧
    -- (2) 定义 6.2
    (∀ (B : ℚ) (f : ℚ → ℚ) (g : ℚ),
      IsGap B f g ↔ CoherentOnBox B g f ∧ ∀ δ : ℚ, CoherentOnBox B δ f → g ≤ δ) ∧
    -- (3) 定理 6.5：gap = (c/a+1)²
    (∀ (a c : ℚ), 0 < a → 0 ≤ c → c ≤ a →
      IsGap 1 (reluAffine a c) ((c / a + 1) ^ 2)) ∧
    -- (4) 定理 6.6：两端 1 与 4
    (∀ (a : ℚ), 0 < a → IsGap 1 (reluAffine a 0) 1 ∧ IsGap 1 (reluAffine a a) 4) :=
  ⟨fun _ _ _ => Iff.rfl,
   fun _ _ _ => Iff.rfl,
   fun a c ha hc0 hc => reluAffine_isGap a c ha hc0 hc,
   fun a ha => ⟨reluAffine_isGap_zero a ha, reluAffine_isGap_full a ha⟩⟩

-- ============ gap 的复合律 ============

/-
  【两层的 gap 怎么叠？】

  单层已经有精确值：gap = (c/a + 1)²（v218）。

  两层呢？直觉上可能是相加或者相乘。**都不是。**

  关键是一个结构事实：**一维的两层 ReLU 塌成一层**。

      max 0 (a₂ · max 0 (a₁x − c₁) − c₂) = max 0 (a₁a₂ · x − (a₂c₁ + c₂))

  证明只用到 a₂ > 0 和 c₂ ≥ 0：当内层被截断时两边都是 0；
  不被截断时就是直接代入。

  于是复合层的 gap 直接由 v218 给出：

      gap(g∘f) = (compThreshold + 1)²,   compThreshold = (c₁ + c₂/a₂)/a₁

  而把它和两层的 gap 对比，得到一个**非加非乘**的律：

      √gap(g∘f) = √gap(f) + (√gap(g) − 1) / a₁

  a₁ = 1 时最干净：

      **√gap(g∘f) = √gap(f) + √gap(g) − 1**

  为什么有个 −1？因为标准 ReLU 的 gap 是 1 而不是 0——
  两层的"1"只该算一次。**这个 −1 就是 v218 那个 1 的减法形式。**

  推论：
  · L 层单位权重的 ReLU，√gap = 1 + Σ cᵢ，即 gap = (1 + Σ cᵢ)²；
  · 标准 ReLU 叠标准 ReLU 还是标准 ReLU（gap 恒为 1）——幂等；
  · 加层不会让 gap 变小（单调）。

  **gap 不可加**：两层 gap 都是 1，复合的 gap 还是 1，不是 4。
-/

-- 两层复合网络：x ↦ max 0 (a₂ · max 0 (a₁x − c₁) − c₂)。
def reluAffine2 (a₁ c₁ a₂ c₂ x : ℚ) : ℚ := reluAffine a₂ c₂ (reluAffine a₁ c₁ x)

-- 复合的坍缩阈值。
def compThreshold (a₁ c₁ a₂ c₂ : ℚ) : ℚ := (c₁ + c₂ / a₂) / a₁

-- 复合参数的恒等式：a₁a₂ x − (a₂c₁ + c₂) = a₂(a₁x − c₁) − c₂。
theorem reluAffine_comp_arg (a₁ c₁ a₂ c₂ x : ℚ) :
    a₁ * a₂ * x - (a₂ * c₁ + c₂) = a₂ * (a₁ * x - c₁) - c₂ := by ring

-- 【结构定理】一维两层 ReLU 塌成一层（权重 a₁a₂，偏置 a₂c₁+c₂）。
theorem reluAffine2_eq_single (a₁ c₁ a₂ c₂ : ℚ) (_h1a : 0 < a₁) (h2a : 0 < a₂)
    (h2c : 0 ≤ c₂) (x : ℚ) :
    reluAffine2 a₁ c₁ a₂ c₂ x = reluAffine (a₁ * a₂) (a₂ * c₁ + c₂) x := by
  have harg := reluAffine_comp_arg a₁ c₁ a₂ c₂ x
  unfold reluAffine2 reluAffine
  rw [harg]
  by_cases h : 0 < a₁ * x - c₁
  · rw [max_eq_right (le_of_lt h)]
  · have h' : a₁ * x - c₁ ≤ 0 := not_lt.mp h
    have hle : a₂ * (a₁ * x - c₁) - c₂ ≤ 0 := by nlinarith
    have hlhs : max 0 (a₂ * max 0 (a₁ * x - c₁) - c₂) = 0 := by
      rw [max_eq_left h', mul_zero]
      exact max_eq_left (by linarith : (0:ℚ) - c₂ ≤ 0)
    have hrhs : max 0 (a₂ * (a₁ * x - c₁) - c₂) = 0 := max_eq_left hle
    rw [hlhs, hrhs]

-- 复合阈值 = 单层的"bias/weight"。
theorem compThreshold_eq (a₁ c₁ a₂ c₂ : ℚ) (h1a : 0 < a₁) (h2a : 0 < a₂) :
    compThreshold a₁ c₁ a₂ c₂ = (a₂ * c₁ + c₂) / (a₁ * a₂) := by
  unfold compThreshold
  field_simp

-- 【两层的 gap】= (compThreshold + 1)²，紧。
theorem gap_two_layer (a₁ c₁ a₂ c₂ : ℚ)
    (h1a : 0 < a₁) (h1c : 0 ≤ c₁) (_h1c' : c₁ ≤ a₁)
    (h2a : 0 < a₂) (h2c : 0 ≤ c₂) (h2c' : c₂ ≤ a₂ * (a₁ - c₁)) :
    (∀ x y : ℚ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 →
      reluAffine2 a₁ c₁ a₂ c₂ x = reluAffine2 a₁ c₁ a₂ c₂ y →
      (x - y) ^ 2 ≤ (compThreshold a₁ c₁ a₂ c₂ + 1) ^ 2) ∧
    (∃ x y : ℚ, -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧
      reluAffine2 a₁ c₁ a₂ c₂ x = reluAffine2 a₁ c₁ a₂ c₂ y ∧
      (x - y) ^ 2 = (compThreshold a₁ c₁ a₂ c₂ + 1) ^ 2) := by
  have hprod : 0 < a₁ * a₂ := mul_pos h1a h2a
  have hb0 : 0 ≤ a₂ * c₁ + c₂ := by nlinarith
  have hb1 : a₂ * c₁ + c₂ ≤ a₁ * a₂ := by nlinarith
  obtain ⟨hu, hw⟩ := reluAffine_gap_exact (a₁ * a₂) (a₂ * c₁ + c₂) hprod hb0 hb1
  have hct := compThreshold_eq a₁ c₁ a₂ c₂ h1a h2a
  constructor
  · intro x y hx1 hx2 hy1 hy2 h
    rw [reluAffine2_eq_single a₁ c₁ a₂ c₂ h1a h2a h2c x,
        reluAffine2_eq_single a₁ c₁ a₂ c₂ h1a h2a h2c y] at h
    have := hu x y hx1 hx2 hy1 hy2 h
    rw [hct]
    exact this
  · obtain ⟨x, y, hx1, hx2, hy1, hy2, hxy, hdist⟩ := hw
    refine ⟨x, y, hx1, hx2, hy1, hy2, ?_, ?_⟩
    · rwa [reluAffine2_eq_single a₁ c₁ a₂ c₂ h1a h2a h2c x,
           reluAffine2_eq_single a₁ c₁ a₂ c₂ h1a h2a h2c y]
    · rw [hct]
      exact hdist

-- 【复合律】√gap(g∘f) = √gap(f) + (√gap(g) − 1)/a₁。
-- （√gap(f) = c₁/a₁ + 1，√gap(g) = c₂/a₂ + 1。）
theorem gap_compose_law (a₁ c₁ a₂ c₂ : ℚ) (h1a : 0 < a₁) (h2a : 0 < a₂) :
    compThreshold a₁ c₁ a₂ c₂ + 1 = (c₁ / a₁ + 1) + ((c₂ / a₂ + 1) - 1) / a₁ := by
  unfold compThreshold
  field_simp
  ring

-- 【单位权重时的复合律】√gap(g∘f) = √gap(f) + √gap(g) − 1。
theorem gap_compose_unit (c₁ c₂ : ℚ) :
    compThreshold 1 c₁ 1 c₂ + 1 = (c₁ + 1) + (c₂ + 1) - 1 := by
  unfold compThreshold
  norm_num
  ring

-- 【不可加】两层 gap 都是 1，复合的 gap 还是 1——不是 4。
theorem gap_not_additive :
    compThreshold 1 0 1 0 + 1 = 1 ∧
      (1 : ℚ) ≠ (0 / 1 + 1) + (0 / 1 + 1) := by
  constructor
  · unfold compThreshold
    norm_num
  · norm_num

-- 【幂等】标准 ReLU 叠标准 ReLU 还是标准 ReLU（gap 恒为 1）。
theorem relu_compose_idempotent (x : ℚ) :
    reluAffine2 1 0 1 0 x = reluAffine 1 0 x := by
  simpa using reluAffine2_eq_single 1 0 1 0 (by norm_num) (by norm_num) (by norm_num) x

-- 【加层不减 gap】复合的 √gap 不小于第一层的 √gap。
theorem gap_depth_monotone (a₁ c₁ a₂ c₂ : ℚ)
    (h1a : 0 < a₁) (h2a : 0 < a₂) (hc1 : 0 ≤ c₁) (hc2 : 0 ≤ c₂) :
    c₁ / a₁ + 1 ≤ compThreshold a₁ c₁ a₂ c₂ + 1 := by
  have h1 : 0 ≤ c₁ / a₁ := div_nonneg hc1 (le_of_lt h1a)
  have h2 : 0 ≤ c₂ / a₂ := div_nonneg hc2 (le_of_lt h2a)
  have h3 : 0 ≤ (c₂ / a₂) / a₁ := div_nonneg h2 (le_of_lt h1a)
  have heq : (c₁ + c₂ / a₂) / a₁ = c₁ / a₁ + (c₂ / a₂) / a₁ := by
    rw [add_div]
  unfold compThreshold
  rw [heq]
  linarith

-- 【打包】两层 ReLU 的 gap 复合律：塌成单层 + 精确值 + 非加性 + 幂等 + 单调。
theorem gap_compose_law_full :
    -- (1) 结构：两层塌成一层
    (∀ a₁ c₁ a₂ c₂ : ℚ, 0 < a₁ → 0 < a₂ → 0 ≤ c₂ → ∀ x : ℚ,
      reluAffine2 a₁ c₁ a₂ c₂ x = reluAffine (a₁ * a₂) (a₂ * c₁ + c₂) x) ∧
    -- (2) 复合律：√gap(g∘f) = √gap(f) + (√gap(g) − 1)/a₁
    (∀ a₁ c₁ a₂ c₂ : ℚ, 0 < a₁ → 0 < a₂ →
      compThreshold a₁ c₁ a₂ c₂ + 1 = (c₁ / a₁ + 1) + ((c₂ / a₂ + 1) - 1) / a₁) ∧
    -- (3) 单位权重：√gap(g∘f) = √gap(f) + √gap(g) − 1
    (∀ c₁ c₂ : ℚ, compThreshold 1 c₁ 1 c₂ + 1 = (c₁ + 1) + (c₂ + 1) - 1) ∧
    -- (4) 幂等
    (∀ x : ℚ, reluAffine2 1 0 1 0 x = reluAffine 1 0 x) ∧
    -- (5) 加层不减
    (∀ a₁ c₁ a₂ c₂ : ℚ, 0 < a₁ → 0 < a₂ → 0 ≤ c₁ → 0 ≤ c₂ →
      c₁ / a₁ + 1 ≤ compThreshold a₁ c₁ a₂ c₂ + 1) :=
  ⟨fun a₁ c₁ a₂ c₂ h1a h2a h2c x => reluAffine2_eq_single a₁ c₁ a₂ c₂ h1a h2a h2c x,
   fun a₁ c₁ a₂ c₂ h1a h2a => gap_compose_law a₁ c₁ a₂ c₂ h1a h2a,
   fun c₁ c₂ => gap_compose_unit c₁ c₂,
   fun x => relu_compose_idempotent x,
   fun a₁ c₁ a₂ c₂ h1a h2a hc1 hc2 => gap_depth_monotone a₁ c₁ a₂ c₂ h1a h2a hc1 hc2⟩

-- ============ 推论 6.14 的形式化：L 层单位权重的闭式 ============

/-
  【L 层复合的 gap = (1 + Σ cᵢ)²】

  由 §6.5 的结构定理（一维两层塌成一层）反复使用：
  L 个 reluAffine 1 cᵢ 的复合，等于单个 reluAffine 1 (Σcᵢ)。

  于是 gap 直接由 reluAffine_isGap 给出：

      gap = ((Σcᵢ)/1 + 1)² = (1 + Σcᵢ)²

  这正是推论 6.14 的内容——之前只有文字陈述，现在有了 Lean 证明。
-/

-- L 层单位权重 ReLU 的复合。
def reluIter : List ℚ → ℚ → ℚ
  | [], x => x
  | c :: cs, x => reluIter cs (reluAffine 1 c x)

-- 【塌成一层】c₀ 加一串，复合 = 单个 reluAffine 1 (c₀ + 其余之和)。
theorem reluIter_eq_single (c₀ : ℚ) (cs : List ℚ)
    (hall : ∀ c ∈ c₀ :: cs, 0 ≤ c) :
    ∀ x : ℚ, reluIter (c₀ :: cs) x = reluAffine 1 (c₀ + cs.sum) x := by
  induction cs generalizing c₀ with
  | nil => intro x; simp [reluIter]
  | cons c₁ rest ih =>
    intro x
    have hall' : ∀ c ∈ c₁ :: rest, 0 ≤ c := fun c hc =>
      hall c (List.mem_cons_of_mem c₀ hc)
    have hc1 : 0 ≤ c₁ := hall c₁ (List.mem_cons_of_mem c₀ List.mem_cons_self)
    have hrest : 0 ≤ rest.sum :=
      List.sum_nonneg (fun c hc => hall' c (List.mem_cons_of_mem c₁ hc))
    show reluIter (c₁ :: rest) (reluAffine 1 c₀ x) = reluAffine 1 (c₀ + (c₁ + rest.sum)) x
    rw [ih c₁ hall' (reluAffine 1 c₀ x)]
    have h := reluAffine2_eq_single 1 c₀ 1 (c₁ + rest.sum) one_pos one_pos
      (by linarith) x
    unfold reluAffine2 at h
    rw [h]
    ring_nf

-- 非空列表版本。
theorem reluIter_eq_single_sum (cs : List ℚ) (hall : ∀ c ∈ cs, 0 ≤ c)
    (hne : cs ≠ []) (x : ℚ) :
    reluIter cs x = reluAffine 1 cs.sum x := by
  cases cs with
  | nil => exact absurd rfl hne
  | cons c₀ rest =>
    rw [reluIter_eq_single c₀ rest hall x, List.sum_cons]

-- 【推论 6.14】L 层单位权重的 gap = (1 + Σcᵢ)²。
theorem reluIter_isGap (cs : List ℚ) (hne : cs ≠ [])
    (h0 : ∀ c ∈ cs, 0 ≤ c) (h1 : cs.sum ≤ 1) :
    IsGap 1 (reluIter cs) ((cs.sum + 1) ^ 2) := by
  have hsum0 : 0 ≤ cs.sum := List.sum_nonneg h0
  have hfun : reluIter cs = reluAffine 1 cs.sum := by
    funext x
    exact reluIter_eq_single_sum cs h0 hne x
  rw [hfun]
  have h := reluAffine_isGap 1 cs.sum one_pos hsum0 h1
  rwa [div_one] at h

-- ============ v228：gap 与泛化 —— 分辨率的闸门 ============

/-
  【§6.10】gap 不只是"可解释性的代价"，它同时是"分辨率的闸门"。

  IsGap B f g 说：f 把距离² ≤ g 的一对输入压成同一个输出。
  所以只要间距 h 满足 h² > g，f 在 h-网格上必须单射——
  一个网格点一个码，一个都省不掉。

  反过来是容量上界：把间距 h 的网格装进盒 [−B,B] 需要 N·h ≤ B；
  而能分辨又要求 h² > g。两式合起来：N²·g < B²。
  **gap 越大，能分辨的点越少。**

  方向值得注意：gap 大 = 函数"简单"（容量小，泛化容易），
  同时 = 信息丢得多（不可解释）。
  **可解释性与泛化不是同向的。**
-/

-- g-分离的有限样本：两两距离平方严格大于 g。
def gSep (g : ℚ) (S : Finset ℚ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → g < (x - y) ^ 2

-- 【§6.10 引理】gap 把 g-分离样本逼成单射。
theorem gSep_injOn {B g : ℚ} {f : ℚ → ℚ} (hg : IsGap B f g)
    {S : Finset ℚ} (hbox : ∀ x ∈ S, |x| ≤ B) (hsep : gSep g S) :
    ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
  intro x hx y hy heq
  by_contra hne
  obtain ⟨hcoh, _⟩ := hg
  have h1 : (x - y) ^ 2 ≤ g := hcoh x y (hbox x hx) (hbox y hy) heq
  have h2 : g < (x - y) ^ 2 := hsep x hx y hy hne
  linarith

-- 等差网格的第 k 点：(k − N)·h，k = 0, …, 2N。
def gridPt (N : ℕ) (h : ℚ) (k : ℕ) : ℚ := ((k : ℚ) - (N : ℚ)) * h

-- 【§6.10 定理】网格间距² > gap ⟹ f 在网格点上单射。
theorem gap_injOn_grid {B g h : ℚ} {f : ℚ → ℚ} (hg : IsGap B f g)
    (hh : 0 < h) (hsep : g < h ^ 2) (N : ℕ)
    (hbox : ∀ k : ℕ, k ≤ 2 * N → |gridPt N h k| ≤ B) :
    ∀ k₁ k₂ : ℕ, k₁ ≤ 2 * N → k₂ ≤ 2 * N →
      f (gridPt N h k₁) = f (gridPt N h k₂) → k₁ = k₂ := by
  intro k₁ k₂ hk1 hk2 heq
  by_contra hne
  obtain ⟨hcoh, _⟩ := hg
  have h1 : (gridPt N h k₁ - gridPt N h k₂) ^ 2 ≤ g :=
    hcoh _ _ (hbox k₁ hk1) (hbox k₂ hk2) heq
  -- 网格点的角标差至少 1。
  have hk : (1 : ℚ) ≤ |(k₁ : ℚ) - (k₂ : ℚ)| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hstep : (1 : ℚ) ≤ (k₂ : ℚ) - (k₁ : ℚ) := by
        have hnat : 1 ≤ k₂ - k₁ := by omega
        have hq : (1 : ℚ) ≤ ((k₂ - k₁ : ℕ) : ℚ) := by exact_mod_cast hnat
        rw [Nat.cast_sub (le_of_lt hlt)] at hq
        exact hq
      have hneg : (k₁ : ℚ) - (k₂ : ℚ) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith
    · have hstep : (1 : ℚ) ≤ (k₁ : ℚ) - (k₂ : ℚ) := by
        have hnat : 1 ≤ k₁ - k₂ := by omega
        have hq : (1 : ℚ) ≤ ((k₁ - k₂ : ℕ) : ℚ) := by exact_mod_cast hnat
        rw [Nat.cast_sub (le_of_lt hlt)] at hq
        exact hq
      rw [abs_of_nonneg (by linarith)]
      exact hstep
  -- 距离² = |Δ|² · h²，而 |Δ| ≥ 1。
  have hdist : gridPt N h k₁ - gridPt N h k₂ = ((k₁ : ℚ) - (k₂ : ℚ)) * h := by
    unfold gridPt; ring
  have hdes : (gridPt N h k₁ - gridPt N h k₂) ^ 2 =
      |(k₁ : ℚ) - (k₂ : ℚ)| ^ 2 * h ^ 2 := by
    rw [hdist, mul_pow, sq_abs]
  rw [hdes] at h1
  have hone : (1 : ℚ) ≤ |(k₁ : ℚ) - (k₂ : ℚ)| ^ 2 := by
    nlinarith [hk]
  have hstep : h ^ 2 ≤ |(k₁ : ℚ) - (k₂ : ℚ)| ^ 2 * h ^ 2 := by
    calc h ^ 2 = 1 * h ^ 2 := by ring
      _ ≤ |(k₁ : ℚ) - (k₂ : ℚ)| ^ 2 * h ^ 2 :=
        mul_le_mul_of_nonneg_right hone (by positivity)
  linarith

-- 【§6.10 推论】容量上界：网格装进盒 + 能分辨 ⟹ N²·g < B²。
theorem gap_capacity_bound {B g h : ℚ} (hB : 0 < B) (hh : 0 < h) (hsep : g < h ^ 2)
    (N : ℕ) (hN : 0 < N) (hspan : (N : ℚ) * h ≤ B) :
    (N : ℚ) ^ 2 * g < B ^ 2 := by
  have h1 : (N : ℚ) ^ 2 * g < (N : ℚ) ^ 2 * h ^ 2 :=
    mul_lt_mul_of_pos_left hsep (by positivity)
  have h2 : (N : ℚ) ^ 2 * h ^ 2 = ((N : ℚ) * h) ^ 2 := by ring
  have hNh : (0 : ℚ) ≤ (N : ℚ) * h := mul_nonneg (by positivity) (le_of_lt hh)
  have h3 : ((N : ℚ) * h) ^ 2 ≤ B ^ 2 := by nlinarith [hspan, hB, hNh]
  linarith

-- 【§6.10 实例】标准 ReLU 的 gap = 1：只能分辨间距 > 1 的网格。
theorem relu_gap_resolution (a : ℚ) (ha : 0 < a) (h : ℚ) (hh : 0 < h) (hsep : 1 < h ^ 2)
    (N : ℕ) (hbox : ∀ k : ℕ, k ≤ 2 * N → |gridPt N h k| ≤ 1) :
    ∀ k₁ k₂ : ℕ, k₁ ≤ 2 * N → k₂ ≤ 2 * N →
      reluAffine a 0 (gridPt N h k₁) = reluAffine a 0 (gridPt N h k₂) → k₁ = k₂ :=
  gap_injOn_grid (reluAffine_isGap_zero a ha) hh hsep N hbox

-- 【§6.10 实例】L 层网络：gap = (Σc + 1)²，分辨率被这个数卡住。
theorem reluIter_gap_resolution (cs : List ℚ) (hne : cs ≠ [])
    (h0 : ∀ c ∈ cs, 0 ≤ c) (h1 : cs.sum ≤ 1)
    (h : ℚ) (hh : 0 < h) (hsep : (cs.sum + 1) ^ 2 < h ^ 2) (N : ℕ)
    (hbox : ∀ k : ℕ, k ≤ 2 * N → |gridPt N h k| ≤ 1) :
    ∀ k₁ k₂ : ℕ, k₁ ≤ 2 * N → k₂ ≤ 2 * N →
      reluIter cs (gridPt N h k₁) = reluIter cs (gridPt N h k₂) → k₁ = k₂ :=
  gap_injOn_grid (reluIter_isGap cs hne h0 h1) hh hsep N hbox

-- ============ v229：容量的精确值与斜率—纤维宽不变量 ============

/-
  【§6.10 续】v228 给的是 N²g < B²（必要条件，且不紧）。
  这里把"紧"补上：等距网格 S_N ⊂ [−B,B] 是 g-分离的，当且仅当

      (N − 1)² · g < 4B²

  即 h = 2B/(N−1) 的网格能分辨 ⟺ h² > g。这就是容量的精确边界，
  且网格本身达到它——上界与达到在同一个式子里。

  再补一条守恒律：reluAffine a c 的 Lipschitz 常数是 a，√gap 是 c/a + 1，
  它们的乘积是 a + c：**斜率 × 纤维宽 = 阈值结构**。调大斜率，
  敏感度上升、纤维变窄，两者互相抵消。
-/

-- 等距网格的第 k 点：−B + k·(2B/(N−1))，k = 0, …, N−1。
def unifPt (B : ℚ) (N : ℕ) (k : ℕ) : ℚ :=
  -B + (k : ℚ) * (2 * B / ((N - 1 : ℕ) : ℚ))

-- 等距网格（N 个点，含两端 −B 与 B）。
def unifGrid (B : ℚ) (N : ℕ) : Finset ℚ :=
  (Finset.range N).image (fun k => unifPt B N k)

-- 网格步长。
def unifStep (B : ℚ) (N : ℕ) : ℚ := 2 * B / ((N - 1 : ℕ) : ℚ)

theorem unifPt_eq (B : ℚ) (N : ℕ) (k : ℕ) :
    unifPt B N k = -B + (k : ℚ) * unifStep B N := rfl

-- 步长为正（N ≥ 2，B > 0）。
theorem unifStep_pos {B : ℚ} {N : ℕ} (hB : 0 < B) (hN : 2 ≤ N) :
    0 < unifStep B N := by
  unfold unifStep
  have h1 : (0 : ℚ) < ((N - 1 : ℕ) : ℚ) := by
    have : 0 < N - 1 := Nat.sub_pos_of_lt hN
    exact_mod_cast this
  positivity

-- 网格点严格递增。
theorem unifPt_strictMono {B : ℚ} {N : ℕ} (hB : 0 < B) (hN : 2 ≤ N) :
    ∀ k₁ k₂ : ℕ, k₁ < k₂ → unifPt B N k₁ < unifPt B N k₂ := by
  intro k₁ k₂ hlt
  rw [unifPt_eq, unifPt_eq]
  have hstep := unifStep_pos hB hN
  have hk : (k₁ : ℚ) < (k₂ : ℚ) := by exact_mod_cast hlt
  nlinarith

-- 网格点数正好是 N。
theorem unifGrid_card {B : ℚ} {N : ℕ} (hB : 0 < B) (hN : 2 ≤ N) :
    (unifGrid B N).card = N := by
  unfold unifGrid
  rw [Finset.card_image_of_injOn]
  · simp
  · intro x _ y _ hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := unifPt_strictMono hB hN x y h
      linarith
    · have := unifPt_strictMono hB hN y x h
      linarith

-- 网格在盒内：所有点满足 |x| ≤ B。
theorem unifGrid_inBox {B : ℚ} {N : ℕ} (hB : 0 < B) (hN : 2 ≤ N) :
    ∀ x ∈ unifGrid B N, |x| ≤ B := by
  intro x hx
  simp only [unifGrid, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [unifPt_eq, abs_le]
  have hstep := unifStep_pos hB hN
  have hkq : (k : ℚ) ≤ ((N - 1 : ℕ) : ℚ) := by
    have : k ≤ N - 1 := by omega
    exact_mod_cast this
  constructor
  · nlinarith [mul_nonneg (Nat.cast_nonneg k) (le_of_lt hstep)]
  · unfold unifStep at *
    have hNq : (0 : ℚ) < ((N - 1 : ℕ) : ℚ) := by
      have : 0 < N - 1 := Nat.sub_pos_of_lt hN
      exact_mod_cast this
    have hlast : ((N - 1 : ℕ) : ℚ) * (2 * B / ((N - 1 : ℕ) : ℚ)) = 2 * B := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right hkq (le_of_lt hstep)]

-- 【§6.10 精确容量】等距网格是 g-分离的 ⟺ (N−1)²g < 4B²。
theorem unifGrid_gSep_iff {B g : ℚ} (hB : 0 < B) (N : ℕ) (hN : 2 ≤ N) :
    gSep g (unifGrid B N) ↔ ((N - 1 : ℕ) : ℚ) ^ 2 * g < 4 * B ^ 2 := by
  have hstep := unifStep_pos hB hN
  have hNq : (0 : ℚ) < ((N - 1 : ℕ) : ℚ) := by
    have : 0 < N - 1 := Nat.sub_pos_of_lt hN
    exact_mod_cast this
  have hstep_sq : unifStep B N ^ 2 = 4 * B ^ 2 / ((N - 1 : ℕ) : ℚ) ^ 2 := by
    unfold unifStep
    field_simp
    norm_num
  constructor
  · -- ⟹：取相邻两点 k = 0 与 k = 1，距离恰为步长。
    intro hsep
    have h0 : unifPt B N 0 ∈ unifGrid B N := by
      simp only [unifGrid, Finset.mem_image, Finset.mem_range]
      exact ⟨0, by omega, rfl⟩
    have h1 : unifPt B N 1 ∈ unifGrid B N := by
      simp only [unifGrid, Finset.mem_image, Finset.mem_range]
      exact ⟨1, by omega, rfl⟩
    have hne : unifPt B N 0 ≠ unifPt B N 1 := by
      have := unifPt_strictMono hB hN 0 1 (by omega)
      linarith
    have h := hsep _ h0 _ h1 hne
    -- 两点距离的平方 = 步长的平方
    have hdiff : (unifPt B N 0 - unifPt B N 1) ^ 2 = unifStep B N ^ 2 := by
      have hneg : unifPt B N 0 - unifPt B N 1 = -(unifStep B N) := by
        rw [unifPt_eq, unifPt_eq]
        push_cast
        ring
      rw [hneg]
      ring
    rw [hdiff] at h
    -- g < h² = 4B²/(N−1)²
    have : ((N - 1 : ℕ) : ℚ) ^ 2 * g < ((N - 1 : ℕ) : ℚ) ^ 2 * unifStep B N ^ 2 :=
      mul_lt_mul_of_pos_left h (by positivity)
    rw [hstep_sq] at this
    have hdiv : ((N - 1 : ℕ) : ℚ) ^ 2 * (4 * B ^ 2 / ((N - 1 : ℕ) : ℚ) ^ 2) = 4 * B ^ 2 := by
      field_simp
    linarith
  · -- ⟸：任意两点相距 ≥ 步长。
    intro hcap x hx y hy hne
    simp only [unifGrid, Finset.mem_image, Finset.mem_range] at hx hy
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    have hkl : k ≠ l := by
      intro h
      exact hne (by rw [h])
    -- |k − l| ≥ 1
    have hstepk : (1 : ℚ) ≤ |(k : ℚ) - (l : ℚ)| := by
      rcases lt_or_gt_of_ne hkl with h | h
      · have : 1 ≤ l - k := by omega
        have hq : (1 : ℚ) ≤ ((l - k : ℕ) : ℚ) := by exact_mod_cast this
        rw [Nat.cast_sub (le_of_lt h)] at hq
        have hneg : (k : ℚ) - (l : ℚ) ≤ 0 := by linarith
        rw [abs_of_nonpos hneg]
        linarith
      · have : 1 ≤ k - l := by omega
        have hq : (1 : ℚ) ≤ ((k - l : ℕ) : ℚ) := by exact_mod_cast this
        rw [Nat.cast_sub (le_of_lt h)] at hq
        rw [abs_of_nonneg (by linarith)]
        exact hq
    -- 距离 = |k−l|·步长
    have hdist : unifPt B N k - unifPt B N l = ((k : ℚ) - (l : ℚ)) * unifStep B N := by
      rw [unifPt_eq, unifPt_eq]
      ring
    have hdes : (unifPt B N k - unifPt B N l) ^ 2 =
        |(k : ℚ) - (l : ℚ)| ^ 2 * unifStep B N ^ 2 := by
      rw [hdist, mul_pow, sq_abs]
    rw [hdes]
    have hone : (1 : ℚ) ≤ |(k : ℚ) - (l : ℚ)| ^ 2 := by nlinarith [hstepk]
    have hge : unifStep B N ^ 2 ≤ |(k : ℚ) - (l : ℚ)| ^ 2 * unifStep B N ^ 2 := by
      calc unifStep B N ^ 2 = 1 * unifStep B N ^ 2 := by ring
        _ ≤ |(k : ℚ) - (l : ℚ)| ^ 2 * unifStep B N ^ 2 :=
          mul_le_mul_of_nonneg_right hone (by positivity)
    -- h² > g，从 (N−1)²g < 4B² 推
    have hh2 : g < unifStep B N ^ 2 := by
      rw [hstep_sq]
      have hdiv : ((N - 1 : ℕ) : ℚ) ^ 2 * (4 * B ^ 2 / ((N - 1 : ℕ) : ℚ) ^ 2) = 4 * B ^ 2 := by
        field_simp
      by_contra hcon
      push Not at hcon
      have : ((N - 1 : ℕ) : ℚ) ^ 2 * g ≥ ((N - 1 : ℕ) : ℚ) ^ 2 *
          (4 * B ^ 2 / ((N - 1 : ℕ) : ℚ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcon (by positivity)
      linarith
    linarith

-- 【§6.10 容量达到】N 点等距网格在盒内、g-分离，故 f 在其上单射。
-- 这就是「容量 = ⌊2B/√g⌋ + 1」的正面一半：网格本身把 N 达到。
theorem gap_capacity_attained {B g : ℚ} (hB : 0 < B) (N : ℕ) (hN : 2 ≤ N)
    (hcap : ((N - 1 : ℕ) : ℚ) ^ 2 * g < 4 * B ^ 2) {f : ℚ → ℚ} (hfg : IsGap B f g) :
    ∃ S : Finset ℚ, S.card = N ∧ (∀ x ∈ S, |x| ≤ B) ∧
      ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
  refine ⟨unifGrid B N, unifGrid_card hB hN, unifGrid_inBox hB hN, ?_⟩
  exact gSep_injOn hfg (unifGrid_inBox hB hN) ((unifGrid_gSep_iff hB N hN).mpr hcap)

-- ===== 斜率—纤维宽不变量 =====

-- 辅助：max 0 · 是 1-Lipschitz。
theorem abs_max_zero_sub_le (u v : ℚ) : |max 0 u - max 0 v| ≤ |u - v| := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · rw [max_eq_right hu, max_eq_right hv]
  · rw [max_eq_right hu, max_eq_left hv, sub_zero, abs_of_nonneg hu,
        abs_of_nonneg (by linarith)]
    linarith
  · rw [max_eq_left hu, max_eq_right hv, zero_sub, abs_neg, abs_of_nonneg hv,
        abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left hu, max_eq_left hv]
    simp

-- 【§6.10 不变量】reluAffine a c 的 Lipschitz 常数是 a（a ≥ 0）。
theorem reluAffine_lipschitz (a c : ℚ) (ha : 0 ≤ a) (x y : ℚ) :
    |reluAffine a c x - reluAffine a c y| ≤ a * |x - y| := by
  unfold reluAffine
  have h := abs_max_zero_sub_le (a * x - c) (a * y - c)
  have hdiff : a * x - c - (a * y - c) = a * (x - y) := by ring
  rw [hdiff, abs_mul, abs_of_nonneg ha] at h
  exact h

-- 【§6.10 守恒律】Lipschitz 常数 × √gap = a + c。
-- 调大斜率 a：敏感度（Lipschitz）上升，纤维（√gap）变窄，乘积不变。
theorem slope_times_gap_width (a c : ℚ) (ha : a ≠ 0) :
    a * (c / a + 1) = a + c := by
  field_simp
  ring

-- 【§6.10 权衡】c > 0 时，gap 关于斜率反单调：a 越大 gap 越小。
theorem gap_decreasing_in_slope {a₁ a₂ c : ℚ} (ha₁ : 0 < a₁) (h12 : a₁ ≤ a₂) (hc : 0 < c) :
    (c / a₂ + 1) ^ 2 ≤ (c / a₁ + 1) ^ 2 := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ h12
  have hdiv : c / a₂ ≤ c / a₁ := by
    apply div_le_div_of_nonneg_left (le_of_lt hc) ha₁ h12
  have h1 : c / a₂ + 1 ≤ c / a₁ + 1 := by linarith
  have h2 : (0 : ℚ) ≤ c / a₂ + 1 := by positivity
  nlinarith

-- ============ v230：η-近似 gap（近似可解释） ============

/-
  【§6.11】精确 gap 要求"输出完全相同"。真实网络不会给出完全相同的输出。
  把等式放松成 |f x − f y| ≤ η，得到 η-近似 gap。

  三条性质：
  1. η = 0 退化为精确 gap（定义 6.1）；
  2. η 增大 ⟹ 要求更强 ⟹ η-gap 不小于精确 gap；
  3. reluAffine 有精确闭式 ((c+η)/a + 1)²——与精确版只差一个 η。

  最有用的推论是线性的：√gap 关于 η 的斜率恒为 1/a。
  **把输出误差换成输入分辨率的汇率，就是权重的倒数。**
-/

-- η-相干：输出差不超过 η 的输入，距离² 不超过 g。
def ApproxCoherent (B g η : ℚ) (f : ℚ → ℚ) : Prop :=
  ∀ x y : ℚ, |x| ≤ B → |y| ≤ B → |f x - f y| ≤ η → (x - y) ^ 2 ≤ g

-- η-近似 gap：相干且最小。
def IsApproxGap (B η : ℚ) (f : ℚ → ℚ) (g : ℚ) : Prop :=
  ApproxCoherent B g η f ∧ ∀ δ : ℚ, ApproxCoherent B δ η f → g ≤ δ

-- η = 0 时，η-相干就是精确相干。
theorem approxCoherent_zero_iff (B g : ℚ) (f : ℚ → ℚ) :
    ApproxCoherent B g 0 f ↔ CoherentOnBox B g f := by
  constructor
  · intro h x y hx hy hxy
    exact h x y hx hy (by rw [hxy, sub_self, abs_zero])
  · intro h x y hx hy hxy
    have h0 : f x = f y := by
      have hab : |f x - f y| = 0 := le_antisymm hxy (abs_nonneg _)
      have := abs_eq_zero.mp hab
      linarith
    exact h x y hx hy h0

-- η 越小条件越强（η 增大时更多对落入"同类"）。
theorem approxCoherent_mono {B g η₁ η₂ : ℚ} (h : η₁ ≤ η₂) {f : ℚ → ℚ}
    (hcoh : ApproxCoherent B g η₂ f) : ApproxCoherent B g η₁ f :=
  fun x y hx hy hxy => hcoh x y hx hy (le_trans hxy h)

-- 近似 gap 不小于精确 gap（η ≥ 0 时，等式是 ≤ η 的特例）。
theorem approxGap_ge_gap {B η g g₀ : ℚ} {f : ℚ → ℚ} (hη : 0 ≤ η)
    (hg : IsGap B f g₀) (hag : IsApproxGap B η f g) : g₀ ≤ g := by
  have hcoh : CoherentOnBox B g f := by
    intro x y hx hy heq
    exact hag.1 x y hx hy (by rw [heq, sub_self, abs_zero]; exact hη)
  exact hg.2 g hcoh

-- 【§6.11 上界】reluAffine a c 的 η-相干界：((c+η)/a + 1)²。
theorem reluAffine_approxGap_upper (a c η : ℚ) (ha : 0 < a) (_hc0 : 0 ≤ c) (hη : 0 ≤ η)
    (x y : ℚ) (_hx1 : -1 ≤ x) (_hx2 : x ≤ 1) (_hy1 : -1 ≤ y) (_hy2 : y ≤ 1)
    (hxy : |reluAffine a c x - reluAffine a c y| ≤ η) :
    (x - y) ^ 2 ≤ ((c + η) / a + 1) ^ 2 := by
  -- 只需证 |x − y| ≤ M，其中 M = (c+η)/a + 1。
  have hM : (0 : ℚ) ≤ (c + η) / a + 1 := by positivity
  have hmain : ∀ u v : ℚ, -1 ≤ u → u ≤ 1 → -1 ≤ v → v ≤ 1 →
      reluAffine a c u - reluAffine a c v ≤ η → u - v ≤ (c + η) / a + 1 := by
    intro u v hu1 _hu2 hv1 _hv2 hd
    by_cases hu : 0 < a * u - c
    · have hum : max 0 (a * u - c) = a * u - c := max_eq_right (le_of_lt hu)
      by_cases hv : 0 < a * v - c
      · have hvm : max 0 (a * v - c) = a * v - c := max_eq_right (le_of_lt hv)
        unfold reluAffine at hd
        rw [hum, hvm] at hd
        have h2 : u - v ≤ η / a := by
          rw [le_div_iff₀ ha]
          linarith
        have hc : η / a ≤ (c + η) / a + 1 := by
          have : (0 : ℚ) ≤ c / a + 1 := by positivity
          have hsplit : (c + η) / a = c / a + η / a := by rw [add_div]
          linarith
        linarith
      · have hv' : a * v - c ≤ 0 := not_lt.mp hv
        have hvm : max 0 (a * v - c) = 0 := max_eq_left hv'
        unfold reluAffine at hd
        rw [hum, hvm] at hd
        have hupper : u ≤ (c + η) / a := by
          rw [le_div_iff₀ ha]
          linarith
        linarith
    · -- u 在坍缩区
      have hu' : a * u - c ≤ 0 := not_lt.mp hu
      have hupper : u ≤ c / a := by
        rw [le_div_iff₀ ha]
        linarith
      have hc : c / a ≤ (c + η) / a := by
        apply div_le_div_of_nonneg_right (by linarith) (le_of_lt ha)
      linarith
  -- 两个方向。
  have h1 : x - y ≤ (c + η) / a + 1 :=
    hmain x y _hx1 _hx2 _hy1 _hy2 (le_trans (le_abs_self _) hxy)
  have h2 : y - x ≤ (c + η) / a + 1 := by
    have hstep : reluAffine a c y - reluAffine a c x ≤
        |reluAffine a c x - reluAffine a c y| := by
      have h := neg_le_abs (reluAffine a c x - reluAffine a c y)
      linarith
    exact hmain y x _hy1 _hy2 _hx1 _hx2 (le_trans hstep hxy)
  have hsq : (x - y) ^ 2 = |x - y| ^ 2 := by rw [sq_abs]
  rw [hsq]
  have habs : |x - y| ≤ (c + η) / a + 1 := by
    rw [abs_le]
    exact ⟨by linarith, h1⟩
  nlinarith [habs, hM, abs_nonneg (x - y)]

-- 【§6.11 见证】x = (c+η)/a 与 y = −1：输出差恰为 η，距离正好是 ((c+η)/a + 1)²。
theorem reluAffine_approxGap_witness (a c η : ℚ) (ha : 0 < a) (hc0 : 0 ≤ c) (hη : 0 ≤ η)
    (hc : c + η ≤ a) :
    ∃ x y : ℚ, -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧
      |reluAffine a c x - reluAffine a c y| ≤ η ∧
      (c + η) / a + 1 ≤ |x - y| := by
  have hca0 : 0 ≤ (c + η) / a := div_nonneg (by linarith) (le_of_lt ha)
  have hca1 : (c + η) / a ≤ 1 := by
    rw [div_le_iff₀ ha]
    linarith
  refine ⟨(c + η) / a, -1, by linarith, hca1, by norm_num, by norm_num, ?_, ?_⟩
  · -- f((c+η)/a) = η，f(−1) = 0
    have hpos : 0 ≤ a * ((c + η) / a) - c := by
      rw [mul_div_cancel₀ (c + η) (ne_of_gt ha)]
      linarith
    have hxval : reluAffine a c ((c + η) / a) = η := by
      unfold reluAffine
      rw [max_eq_right hpos, mul_div_cancel₀ (c + η) (ne_of_gt ha)]
      ring
    have hneg : a * (-1) - c ≤ 0 := by nlinarith
    have hyval : reluAffine a c (-1) = 0 := by
      unfold reluAffine
      rw [max_eq_left hneg]
    rw [hxval, hyval, sub_zero, abs_of_nonneg hη]
  · have h2 : (0 : ℚ) ≤ (c + η) / a - (-1) := by linarith
    rw [abs_of_nonneg h2]
    linarith

-- 【§6.11 精确值】reluAffine a c 的 η-gap = ((c+η)/a + 1)²。
theorem reluAffine_isApproxGap (a c η : ℚ) (ha : 0 < a) (hc0 : 0 ≤ c) (hη : 0 ≤ η)
    (hc : c + η ≤ a) :
    IsApproxGap 1 η (reluAffine a c) (((c + η) / a + 1) ^ 2) := by
  constructor
  · intro x y hx hy hxy
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    exact reluAffine_approxGap_upper a c η ha hc0 hη x y hx1 hx2 hy1 hy2 hxy
  · intro δ hδ
    obtain ⟨x, y, hx1, hx2, hy1, hy2, hdiff, hdist⟩ :=
      reluAffine_approxGap_witness a c η ha hc0 hη hc
    have hx : |x| ≤ 1 := abs_le.mpr ⟨hx1, hx2⟩
    have hy : |y| ≤ 1 := abs_le.mpr ⟨hy1, hy2⟩
    have h1 : (x - y) ^ 2 ≤ δ := hδ x y hx hy hdiff
    have h2 : (x - y) ^ 2 ≤ ((c + η) / a + 1) ^ 2 :=
      reluAffine_approxGap_upper a c η ha hc0 hη x y hx1 hx2 hy1 hy2 hdiff
    have h3 : ((c + η) / a + 1) ^ 2 ≤ (x - y) ^ 2 := by
      have hsq : (x - y) ^ 2 = |x - y| ^ 2 := by rw [sq_abs]
      rw [hsq]
      have hM : (0 : ℚ) ≤ (c + η) / a + 1 := by positivity
      nlinarith [hdist, abs_nonneg (x - y)]
    linarith

-- 【§6.11 线性律】√gap 关于 η 的斜率恒为 1/a。
theorem approxGap_slope (a c η : ℚ) (ha : a ≠ 0) :
    ((c + η) / a + 1) - (c / a + 1) = η / a := by
  field_simp
  ring

-- 退化检查：η = 0 时，η-gap 恰好退回精确 gap。
theorem approxGap_zero_eq (a c : ℚ) :
    ((c + 0) / a + 1) ^ 2 = (c / a + 1) ^ 2 := by
  norm_num

-- ============ v231：多维 gap —— 维度的代价 ============

/-
  【§6.12】§6.9 说多维很难，因为坍缩集变成凸块之并。
  但有一类多维情形仍然算得清：**整个盒被压成一点**。

  这给出维度的第一个定量结果：
      盒 [−B,B]ⁿ 的直径平方 = 4nB²
  所以多维 ReLU 的 gap 上界是 4nB²，而且当整个盒坍缩时**恰好达到**。

  一维时 n = 1，退回 4B²，与 §6.4 的 "ReLU 杀死整个盒 ⟹ gap = 4" 一致。
  **维度让 gap 线性增长：高维网络天生更难解释，这不是权重的问题，是几何。**
-/

-- 多维平方距离（与 commonDist 同构，但作用在裸坐标上）。
def sqDist {n : ℕ} (x y : Fin n → ℚ) : ℚ := ∑ i, (x i - y i) ^ 2

-- 多维相干：盒内两个同输出的输入，平方距离不超过 δ。
def CoherentOnBoxND {n : ℕ} (B δ : ℚ) (f : (Fin n → ℚ) → ℚ) : Prop :=
  ∀ x y : Fin n → ℚ, (∀ i, |x i| ≤ B) → (∀ i, |y i| ≤ B) → f x = f y → sqDist x y ≤ δ

-- 多维 gap：相干且最小。
def IsGapND {n : ℕ} (B : ℚ) (f : (Fin n → ℚ) → ℚ) (g : ℚ) : Prop :=
  CoherentOnBoxND B g f ∧ ∀ δ : ℚ, CoherentOnBoxND B δ f → g ≤ δ

-- 【§6.12 引理】盒内任意两点的平方距离不超过直径平方 4nB²。
theorem sqDist_bound {n : ℕ} {B : ℚ} {x y : Fin n → ℚ}
    (hx : ∀ i, |x i| ≤ B) (hy : ∀ i, |y i| ≤ B) :
    sqDist x y ≤ 4 * n * B ^ 2 := by
  unfold sqDist
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)), (x i - y i) ^ 2 ≤ 4 * B ^ 2 := by
    intro i _
    have h1 := abs_le.mp (hx i)
    have h2 := abs_le.mp (hy i)
    nlinarith [sq_nonneg (x i - y i)]
  calc ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin n, 4 * B ^ 2 := Finset.sum_le_sum hterm
    _ = 4 * n * B ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

-- 【§6.12 定理】整个盒被压成一点时，多维 gap 恰好是盒的直径平方。
theorem relu_multi_isGap_full {n : ℕ} (_hn : 0 < n) {B : ℚ} (hB : 0 < B)
    (w : Fin n → ℚ) (c : ℚ) (hw : ∀ i, 0 ≤ w i) (hc : B * ∑ i, w i ≤ c) :
    IsGapND B (fun x => max 0 (∑ i, w i * x i - c)) (4 * n * B ^ 2) := by
  have hsum_nonneg : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  constructor
  · -- 上界：任何一对同输出的点，距离平方 ≤ 直径平方。
    intro x y hx hy _
    exact sqDist_bound hx hy
  · -- 达到：全 B 与全 −B 都被压成 0。
    intro δ hδ
    -- 两个端点
    have hx_box : ∀ i : Fin n, |(fun _ : Fin n => B) i| ≤ B := by
      intro i
      rw [abs_of_nonneg (le_of_lt hB)]
    have hy_box : ∀ i : Fin n, |(fun _ : Fin n => -B) i| ≤ B := by
      intro i
      have : (-B : ℚ) ≤ 0 := by linarith
      rw [abs_of_nonpos this]
      linarith
    -- 记 S = Σ w i
    have hsumB : ∑ i, w i * B = (∑ i, w i) * B := by rw [Finset.sum_mul]
    have hsumN : ∑ i, w i * (-B) = -((∑ i, w i) * B) := by
      have h1 : ∀ i : Fin n, w i * (-B) = -(w i * B) := by
        intro i; ring
      simp only [h1]
      rw [Finset.sum_neg_distrib, hsumB]
    have hSB_nonneg : 0 ≤ (∑ i, w i) * B := mul_nonneg hsum_nonneg (le_of_lt hB)
    -- f(全 B) = 0
    have hfx : max 0 (∑ i, w i * B - c) = 0 := by
      apply max_eq_left
      rw [hsumB]
      linarith
    -- f(全 −B) = 0
    have hfy : max 0 (∑ i, w i * (-B) - c) = 0 := by
      apply max_eq_left
      rw [hsumN]
      linarith
    have hsame := hδ (fun _ => B) (fun _ => -B) hx_box hy_box (by
      show max 0 (∑ i, w i * B - c) = max 0 (∑ i, w i * (-B) - c)
      rw [hfx, hfy])
    -- 距离恰为 4nB²
    have hdist : sqDist (fun _ : Fin n => B) (fun _ : Fin n => -B) = 4 * n * B ^ 2 := by
      unfold sqDist
      have hterm : ∀ i : Fin n, ((fun _ : Fin n => B) i - (fun _ : Fin n => -B) i) ^ 2 =
          4 * B ^ 2 := by
        intro i
        simp only
        ring
      calc ∑ i, ((fun _ : Fin n => B) i - (fun _ : Fin n => -B) i) ^ 2
          = ∑ _i : Fin n, 4 * B ^ 2 := Finset.sum_congr rfl (fun i _ => hterm i)
        _ = 4 * n * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
    rwa [hdist] at hsame

-- 一维核对：n = 1 时 4nB² = 4B²，与 §6.4 的"整盒坍缩 ⟹ gap = 4"一致。
theorem multi_gap_dim1 (B : ℚ) : 4 * (1 : ℕ) * B ^ 2 = 4 * B ^ 2 := by
  norm_num

-- ============ v232：尺度不变性的精确范围 ============

/-
  【§8.3 预言一的边界】"gap 与权重整体尺度无关"只在**层内**成立。

  (1) 层内：同时缩放 (a, c) → (λa, λc)，gap 不变。
  (2) 跨层：缩放第一层会把第二层的贡献除以 λ。
  (3) 于是整个网络**不是**尺度不变的。

  这不是补丁，是一条正面结论：**放大浅层权重，会让深层贡献被稀释，
  整个网络更可解释**。预言一应该在层内被检验，不是在网络层。
-/

-- (1) 层内尺度不变：gap(c·lam, a·lam) = gap(c, a)。
theorem gap_layer_scale_invariant (a c lam : ℚ) (_ha : a ≠ 0) (hlam : lam ≠ 0) :
    ((lam * c) / (lam * a) + 1) ^ 2 = (c / a + 1) ^ 2 := by
  rw [mul_div_mul_left c a hlam]

-- (2) 跨层协变：两层复合的 √gap（单位阈值形式）。
def sqrtGapTwo (a₁ c₁ a₂ c₂ : ℚ) : ℚ := c₁ / a₁ + 1 + c₂ / (a₂ * a₁)

-- 缩放第一层后，第二层的贡献被 lam 除。
theorem sqrtGapTwo_scale_first (a₁ c₁ a₂ c₂ lam : ℚ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlam : lam ≠ 0) :
    sqrtGapTwo (lam * a₁) (lam * c₁) a₂ c₂ =
      c₁ / a₁ + 1 + (c₂ / (a₂ * a₁)) / lam := by
  unfold sqrtGapTwo
  have h1 : (lam * c₁) / (lam * a₁) = c₁ / a₁ := mul_div_mul_left c₁ a₁ hlam
  have h2 : a₂ * (lam * a₁) = lam * (a₂ * a₁) := by ring
  rw [h1, h2]
  field_simp

-- (3) 整个网络的 gap 不是尺度不变的。
theorem network_gap_scale_dependent :
    ∃ (a₁ c₁ a₂ c₂ lam : ℚ), 0 < a₁ ∧ 0 < a₂ ∧ 0 < lam ∧
      sqrtGapTwo a₁ c₁ a₂ c₂ ≠ sqrtGapTwo (lam * a₁) (lam * c₁) a₂ c₂ := by
  refine ⟨1, 0, 1, 1, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold sqrtGapTwo
  norm_num

-- 推论：放大第一层权重，复合 gap 单调下降（lam 越大越可解释）。
theorem sqrtGapTwo_scale_first_le {a₁ c₁ a₂ c₂ lam : ℚ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hc₂ : 0 ≤ c₂) (hlam : 1 ≤ lam) :
    sqrtGapTwo (lam * a₁) (lam * c₁) a₂ c₂ ≤ sqrtGapTwo a₁ c₁ a₂ c₂ := by
  unfold sqrtGapTwo
  have hA : (0 : ℚ) < a₂ * a₁ := mul_pos ha₂ ha₁
  have h1 : (lam * c₁) / (lam * a₁) = c₁ / a₁ := by
    apply mul_div_mul_left
    linarith
  have h2 : a₂ * (lam * a₁) = lam * (a₂ * a₁) := by ring
  rw [h1, h2]
  have h3 : c₂ / (lam * (a₂ * a₁)) ≤ c₂ / (a₂ * a₁) := by
    apply div_le_div_of_nonneg_left hc₂ hA
    nlinarith
  linarith

-- ============ v233：SquareFlat 与 gap 测相反方向（§7.7.1 的例证） ============

/-
  SquareFlat（不放大）与 gap（不折叠太远）方向相反，互不推出。
  两个极简例证：
  - 常数映射：不放大任何距离（平坦），但 gap = 4 —— 整个盒折叠成一点。
  - x ↦ 2x：放大 2 倍（不平坦），但 gap = 0 —— 不折叠任何东西。
-/

-- 常数映射的 gap = 4（盒 [−1,1] 的直径平方）。
theorem const_isGap (c : ℚ) : IsGap 1 (fun _ : ℚ => c) 4 := by
  constructor
  · intro x y hx hy _
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    nlinarith [sq_nonneg (x - y)]
  · intro δ hδ
    have hx : |(1 : ℚ)| ≤ 1 := by norm_num
    have hy : |(-1 : ℚ)| ≤ 1 := by norm_num
    have h := hδ 1 (-1) hx hy rfl
    have h4 : ((1 : ℚ) - (-1)) ^ 2 = 4 := by norm_num
    linarith

-- x ↦ 2x 的 gap = 0（单射，不折叠任何东西，尽管它放大 2 倍）。
theorem scale_two_isGap : IsGap 1 (fun x : ℚ => 2 * x) 0 := by
  constructor
  · intro x y _ _ hxy
    have hxy' : x = y := by linarith
    rw [hxy']
    norm_num
  · intro δ hδ
    have hx : |(0 : ℚ)| ≤ 1 := by norm_num
    have h := hδ 0 0 hx hx rfl
    simpa using h

-- ============ v234：为什么 gap 是关系而不是函数 ============

/-
  【§9.1.4】可行阈值集合 V = {δ : CoherentOnBox B δ f} 是一个上闭集。
  V 有最小元 ⟺ S（坍缩距离平方集）在 ℚ 中有上确界且属于 ℚ。
  ℚ 不完备，所以这一步可能失败——这就是 gap 写成关系的理由，
  而不是笼统的"没有完备性"。
-/

-- 可行阈值是上闭的：δ 可行则更大的也可行。
theorem coherentOnBox_mono {B δ δ' : ℚ} {f : ℚ → ℚ}
    (h : CoherentOnBox B δ f) (hle : δ ≤ δ') : CoherentOnBox B δ' f := by
  intro x y hx hy hxy
  exact le_trans (h x y hx hy hxy) hle

-- 若 gap 存在，则唯一（上闭集的最小元至多一个）。
theorem isGap_unique {B g g' : ℚ} {f : ℚ → ℚ}
    (hg : IsGap B f g) (hg' : IsGap B f g') : g = g' := by
  have h1 : g ≤ g' := hg.2 g' hg'.1
  have h2 : g' ≤ g := hg'.2 g hg.1
  linarith

-- ============ 层族与映射之间的桥 ============

/-
  【Coherent 和 CoherentMap 到底是不是同一件事？】

  论文的 §4 和 §5 用两个"相干"：

      Coherent    (L : LayerLadder) (n : ℕ) (f : NetState L n)      -- 层族
      CoherentMap (δ : ℚ)           (f : StateQuant n → StateQuant m) -- 映射

  直觉上以为它们刻画同一件事。**不是。**

  **一个令人不舒服的定理**（observation_always_coherent）：
  取任意映射 F 和一个输入 x，把每层都定义成 "F x 在 δ_i 下的凝结像"，
  得到的层族**永远相干**——因为每层都是同一个值的像。

  也就是说：**Coherent 单独不携带任何关于网络的信息。**
  它的内容全部在"每层用的是**不同**的映射"这句话里。

  所以正确的网络模型是**逐层的映射族** `fs : Fin L.m → (StateQuant n → StateQuant n)`，
  而不是单个端到端映射。层 i 的激活是 `fs i x`。

  在这个模型下，有一个干净的翻译（layerState_coherent_iff）：

      **层族相干  ⟺  对一切 i ≤ j，fs i x 与 fs j x 在层 δ_i 下同层**

  这就是论文 §4↔§5 需要的桥：把 `Coherent` 展开成
  一条关于**距离**（`ResLayer.related` ← `commonDist ≤ δ`）的条件。

  而 `CoherentMap` 与它的关系是单向的：
  `CoherentMap` 说的是"相同输出 ⟹ 输入近"，
  它**不**给出"输入近 ⟹ 输出近"。所以两者不能互相推出——
  v203 的 `gap_compose_left` 只在否命题方向成立，正是这个原因。
-/

-- 层 i 的对象：把 `fs i x` 凝结到层 δ_i。
def layerState (L : LayerLadder) {n : ℕ}
    (fs : Fin L.m → StateQuant n → StateQuant n) (x : StateQuant n) : NetState L n :=
  fun i => Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (fs i x)

-- 距离 ≤ 阈值 ⟹ 同层（不可区分的单步）。
theorem ResLayer.related_of_le {δ : ℚ} {n : ℕ} {x y : StateQuant n}
    (h : commonDist x y ≤ δ) : ResLayer.related ⟨δ⟩ x y :=
  Relation.ReflTransGen.single h

-- 【桥】层族相干 ⟺ 任意两层 i ≤ j 的激活在层 δ_i 下同层。
theorem layerState_coherent_iff (L : LayerLadder) {n : ℕ}
    (fs : Fin L.m → StateQuant n → StateQuant n) (x : StateQuant n) :
    Coherent L n (layerState L fs x) ↔
      ∀ (i j : Fin L.m) (_ : i ≤ j), ResLayer.related ⟨L.δ i⟩ (fs j x) (fs i x) := by
  constructor
  · intro hc i j hij
    have h := hc i j hij
    have h' : (Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (fs j x) : ResLayer.object ⟨L.δ i⟩ n)
        = Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (fs i x) := by
      simpa only [layerState, ResLayer.resolution_condense] using h
    exact Quotient.exact h'
  · intro h i j hij
    show ResLayer.resolution (L.le_delta hij)
        (Quotient.mk (ResLayer.condense ⟨L.δ j⟩) (fs j x))
      = Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (fs i x)
    rw [ResLayer.resolution_condense]
    exact Quotient.sound (h i j hij)

-- 【充分条件】每层的激活互相在 δ_i 内 ⟹ 层族相干。
theorem layerState_coherent_of_close (L : LayerLadder) {n : ℕ}
    (fs : Fin L.m → StateQuant n → StateQuant n) (x : StateQuant n)
    (h : ∀ (i j : Fin L.m) (_ : i ≤ j), commonDist (fs j x) (fs i x) ≤ L.δ i) :
    Coherent L n (layerState L fs x) :=
  (layerState_coherent_iff L fs x).mpr
    (fun i j hij => ResLayer.related_of_le (h i j hij))

-- 【不相干的见证】不相干 ⟹ 存在一对层，激活在 δ_i 下不同层。
theorem layerState_incoherent_witness (L : LayerLadder) {n : ℕ}
    (fs : Fin L.m → StateQuant n → StateQuant n) (x : StateQuant n)
    (h : ¬ Coherent L n (layerState L fs x)) :
    ∃ (i j : Fin L.m) (_ : i ≤ j), ¬ ResLayer.related ⟨L.δ i⟩ (fs j x) (fs i x) := by
  by_contra hc
  push Not at hc
  exact h ((layerState_coherent_iff L fs x).mpr hc)

-- 【观测自相干】任何映射按层塔观测都相干——`Coherent` 单独不携带网络信息。
theorem observation_always_coherent (L : LayerLadder) {n : ℕ}
    (F : StateQuant n → StateQuant n) (x : StateQuant n) :
    Coherent L n (fun i => Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (F x)) := by
  intro i j _
  rw [ResLayer.resolution_condense]

-- 【打包】层族判据的完整翻译：桥 + 充分条件 + 见证 + 观测自相干。
theorem layer_bridge :
    -- (1) 相干 ⟺ 逐层同层
    (∀ (L : LayerLadder) {n : ℕ} (fs : Fin L.m → StateQuant n → StateQuant n)
        (x : StateQuant n),
      Coherent L n (layerState L fs x) ↔
        ∀ (i j : Fin L.m) (_ : i ≤ j), ResLayer.related ⟨L.δ i⟩ (fs j x) (fs i x)) ∧
    -- (2) 距离条件 ⟹ 相干
    (∀ (L : LayerLadder) {n : ℕ} (fs : Fin L.m → StateQuant n → StateQuant n)
        (x : StateQuant n),
      (∀ (i j : Fin L.m) (_ : i ≤ j), commonDist (fs j x) (fs i x) ≤ L.δ i) →
      Coherent L n (layerState L fs x)) ∧
    -- (3) 不相干 ⟹ 有一对层不同层
    (∀ (L : LayerLadder) {n : ℕ} (fs : Fin L.m → StateQuant n → StateQuant n)
        (x : StateQuant n),
      ¬ Coherent L n (layerState L fs x) →
      ∃ (i j : Fin L.m) (_ : i ≤ j), ¬ ResLayer.related ⟨L.δ i⟩ (fs j x) (fs i x)) ∧
    -- (4) 单映射无法产生不相干
    (∀ (L : LayerLadder) {n : ℕ} (F : StateQuant n → StateQuant n) (x : StateQuant n),
      Coherent L n (fun i => Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (F x))) :=
  ⟨fun L _ fs x => layerState_coherent_iff L fs x,
   fun L _ fs x h => layerState_coherent_of_close L fs x h,
   fun L _ fs x h => layerState_incoherent_witness L fs x h,
   fun L _ F x => observation_always_coherent L F x⟩

-- ============ 计算网格：b₁ 度量扩张 ============

/-
  【他们那个方格，在我们的框架里是什么？】

  v221 确认了：2610.17117 的方格问的是"层变换是否与改述等价交换"。
  这里把它翻译成我们的语言，看能不能算出来。

  **方格的定义**：一个层变换 T 在层 δ 上是"平的"，如果不把 δ-等价对推成非等价：

      SquareFlat δ T  :=  ∀ x y, commonDist x y ≤ δ → commonDist (T x) (T y) ≤ δ

  于是：

  · **id 平坦**（什么都不动）；
  · **复合保持平坦**（两个平的叠起来还是平的）；
  · **收缩层平坦**：|c| ≤ 1 时 `scale c` 不放大距离；
  · **ReLU 平坦**：ReLU 是 1-Lipschitz，永不放大；
  · **扩张层不平坦**：|c| > 1 时 `scale c` 把 δ-等价对推出去。

  核心定理（δ = 1 时最干净）：

      **SquareFlat 1 (scale c)  ⟺  c² ≤ 1**

  **这就是 b₁ 的几何意义**：

  收缩的层变换不产生环；扩张的层变换每出现一次，就有一个方格不平，
  b₁ 加一。

  而 transformer 的层不是收缩的（权重矩阵的谱范数一般 > 1），
  所以他们的 b₁ = N(L−1) 有内容；我们的 `id` / `ReLU` 层没有。

  **这不是"解释他们的结果"，是把同一个问题在我们这边算了一遍。**
-/

-- 【计算方格】层变换 T 在层 δ 上是平的：不把 δ-等价对推成非等价。
def SquareFlat {n : ℕ} (δ : ℚ) (T : StateQuant n → StateQuant n) : Prop :=
  ∀ x y, commonDist x y ≤ δ → commonDist (T x) (T y) ≤ δ

-- 恒等层平坦。
theorem squareFlat_id {n : ℕ} (δ : ℚ) :
    SquareFlat δ (id : StateQuant n → StateQuant n) :=
  fun _ _ h => h

-- 平坦在复合下保持。
theorem squareFlat_comp {n : ℕ} {δ : ℚ} {T₁ T₂ : StateQuant n → StateQuant n}
    (h₁ : SquareFlat δ T₁) (h₂ : SquareFlat δ T₂) :
    SquareFlat δ (T₂ ∘ T₁) :=
  fun x y h => h₂ _ _ (h₁ x y h)

-- ReLU 的 1-Lipschitz 性。
theorem relu_lipschitz (a b : ℚ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · rw [max_eq_right ha, max_eq_right hb]
  · have hb' : b < 0 := not_le.mp hb
    rw [max_eq_right ha, max_eq_left (le_of_lt hb'), sub_zero, abs_of_nonneg ha]
    have : |a - b| = a - b := abs_of_nonneg (by linarith)
    rw [this]
    linarith
  · have ha' : a < 0 := not_le.mp ha
    have hlt : a - b < 0 := by linarith
    rw [max_eq_left (le_of_lt ha'), max_eq_right hb, zero_sub, abs_neg, abs_of_nonneg hb]
    have : |a - b| = b - a := by rw [abs_of_neg hlt]; ring
    rw [this]
    linarith
  · have ha' : a < 0 := not_le.mp ha
    have hb' : b < 0 := not_le.mp hb
    rw [max_eq_left (le_of_lt ha'), max_eq_left (le_of_lt hb'), sub_self, abs_zero]
    exact abs_nonneg _

-- 平方版：ReLU 不放大平方距离。
theorem relu_sq_lipschitz (a b : ℚ) : (relu a - relu b) ^ 2 ≤ (a - b) ^ 2 :=
  sq_le_sq.mpr (relu_lipschitz a b)

-- 【ReLU 层平坦】永不破方格。
theorem squareFlat_relu (δ : ℚ) : SquareFlat (n := 1) δ (reluState) := by
  intro x y hxy
  rw [commonDist_one] at hxy ⊢
  exact le_trans (relu_sq_lipschitz (x.val 0) (y.val 0)) hxy

-- ============ 附范畴：二值的内部结构 ============

/-
  【附范畴：二值不是裸的】

  用户的观察（2026-11-15）："一切逻辑貌似可以用二值来写，
  不过二值不只是单纯的 0/1，内在存在附范畴。若附范畴作用，
  形成的复杂结果直接适配暴力计算；既然是暴力计算，
  那么暴力计算计算本身也可以。"

  在理论里，这个"附范畴"就是**相位**：

    · Bool 的两个值（0/1）；
    · 附上符号（正/负）；
    · 得到 Phase 的三个值（正/负/中）。

  所以 Phase = 附范畴的 Bool：1 分裂成"正 1"和"负 1"，0 保持为"中"。
  二值的"位"决定有没有方向，附着的"符号"决定方向朝哪边。

  附范畴的作用 = **符号乘法**（interferenceSign），
  给出一个有限的 3×3 合成表——**直接适配暴力计算**。
  这正是 v164 的"相位 = ℚ 的符号"在做的事。

  而"暴力计算计算本身" = 有限世界的封闭性：

    · 函数空间 (α → β) 在 α、β 有限时是有限的——所以"计算"
      本身是一个有限对象，可以被枚举、被分析；
    · 有限自映射必有周期点（periodic_point_exists）——
      任何计算作用于自身，最终都会循环。

  所以"暴力计算计算本身"不是元层的幻想，而是有限性的一条推论：
  **没有更高阶的不可计算性——所有层都是同一层。**
  这也正是"自我 = 自指的洞"在计算层面的形态：
  计算可以计算计算，因为计算是有限的。
-/

-- 附范畴的底层位：中性 = false，有方向 = true。
def Phase.bit : Phase → Bool
  | .neutral => false
  | .positive => true
  | .negative => true

-- 【附范畴】Phase 就是"带符号的 Bool"：位为假 ⟺ 符号为零。
theorem phase_is_attached_bool : ∀ p : Phase,
    (Phase.bit p = false ↔ phaseSign p = 0) ∧
    (Phase.bit p = true ↔ phaseSign p ≠ 0) := by
  intro p
  cases p <;> simp [Phase.bit, phaseSign]

-- 【附范畴的合成】符号乘法：两个相位的符号之积（有限 3×3 表）。
def phaseMultiply (a b : Phase) : ℚ := phaseSign a * phaseSign b

-- 附范畴的合成表是有限的：乘积只落在 {1, -1, 0} 上。
theorem phaseMultiply_finite (a b : Phase) :
    phaseMultiply a b ∈ ({1, -1, 0} : Finset ℚ) := by
  unfold phaseMultiply phaseSign
  cases a <;> cases b <;> simp

-- 【暴力计算的空间是有限的】有限映射空间仍是有限的。
theorem computation_space_finite {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α :=
  Fintype.card_fun

-- 【暴力计算计算本身】有限自映射必有周期点：任何计算作用于自身都会循环。
theorem computation_self_loop {α : Type*} [Fintype α] [Nonempty α] (compute : α → α) :
    ∃ y, ∃ k : ℕ, 1 ≤ k ∧ compute^[k] y = y :=
  periodic_point_exists compute

-- 【二值 + 附范畴 + 自指】四条合一。
theorem attached_binary_closed :
    (∀ p : Phase, (Phase.bit p = false ↔ phaseSign p = 0) ∧
                   (Phase.bit p = true ↔ phaseSign p ≠ 0)) ∧
    (∀ a b : Phase, phaseMultiply a b ∈ ({1, -1, 0} : Finset ℚ)) ∧
    (∀ (α β : Type) [DecidableEq α] [Fintype α] [Fintype β],
      Fintype.card (α → β) = Fintype.card β ^ Fintype.card α) ∧
    (∀ (α : Type) [Fintype α] [Nonempty α] (f : α → α),
      ∃ y, ∃ k : ℕ, 1 ≤ k ∧ f^[k] y = y) :=
  ⟨phase_is_attached_bool,
   fun a b => phaseMultiply_finite a b,
   fun _ _ _ _ _ => computation_space_finite,
   fun _ _ _ f => computation_self_loop f⟩

-- ============ 附范畴（正名）：二值总是相对于上下文的 ============

/-
  【附范畴：上下文与"排中不绝对"】

  用户 2026-11-15 的澄清：
  "我确实提到上下文，不然为啥叫附范畴。就是话不绝对——
  上下文，上面和下面，就像两块各执一块的拼图，
  没有对方，谁也不能说绝对（排中，或者说排中自体不具备绝对）。
  上下文的范畴联系，即拼接，就像范畴层。
  而附范畴就是试图用二值完成附范畴的建设和编码。"

  所以"附范畴" = **二值 + 上下文**（v204 的"符号"只是上下文的一种）：

    · 二值判定永远不是裸的：它是"在某个层下"的判定；
    · 上下文就是层（ResLayer / LayerLadder 的一层）；
    · 两个上下文互为拼图：没有细层，粗层不知从何凝来；
      没有粗层，细层也不"细"；
    · 上下文的联系 = **拼接** = 消解（resolution）；
    · **排中（P ∨ ¬P）不是绝对的**：同一个二值判定在两个上下文里可以不同。

  "用二值完成附范畴的建设和编码"：
  二值是砖，上下文是砌法，拼起来才是范畴层。
  而范畴层本身就是有限性长出来的——每一层都是商，每一层都是一个视角，
  没有哪个视角是"绝对"的。
-/

-- 上下文中的二值判定：在层 δ 下，x 和 y 是否"相同"。
def sameAt {n : ℕ} (δ : ℚ) (x y : StateQuant n) : Bool :=
  decide (commonDist x y ≤ δ)

-- 【拼接的方向性】细层说"相同"，粗层必然也说"相同"。
-- 反之不成立——这正是排中不绝对的地方。
theorem sameAt_monotone {n : ℕ} {x y : StateQuant n} {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) :
    sameAt δ₁ x y = true → sameAt δ₂ x y = true := by
  unfold sameAt
  intro h1
  rw [decide_eq_true_iff] at h1 ⊢
  exact le_trans h1 h

-- 【排中不绝对】同一个二值判定在两个上下文里可以不同。
theorem excluded_middle_not_absolute :
    ∃ (x y : StateQuant 1) (δ₁ δ₂ : ℚ),
      δ₁ < δ₂ ∧ sameAt δ₁ x y ≠ sameAt δ₂ x y := by
  refine ⟨{ val := fun _ => 0, phase := .neutral },
          { val := fun _ => 2, phase := .neutral }, 1, 10, by norm_num, ?_⟩
  have hcd : commonDist ({ val := fun _ => (0 : ℚ), phase := .neutral } : StateQuant 1)
                        ({ val := fun _ => (2 : ℚ), phase := .neutral } : StateQuant 1) = 4 := by
    rw [commonDist_eq_sum_sq]
    simp only [pairDiff]
    norm_num
  unfold sameAt
  rw [hcd]
  norm_num

-- 【互为拼图】粗层说"相同"、细层说"不同"——两块拼图各执一边。
theorem pieces_depend :
    (∀ {n : ℕ} {x y : StateQuant n} {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ →
      sameAt δ₁ x y = true → sameAt δ₂ x y = true) ∧
    (∃ (x y : StateQuant 1) (δ₁ δ₂ : ℚ), δ₁ < δ₂ ∧
      sameAt δ₁ x y = false ∧ sameAt δ₂ x y = true) := by
  refine ⟨fun h => sameAt_monotone h, ?_⟩
  obtain ⟨x, y, δ₁, δ₂, hlt, hne⟩ := excluded_middle_not_absolute
  refine ⟨x, y, δ₁, δ₂, hlt, ?_, ?_⟩
  · -- sameAt δ₁ 必为 false（由单调性：若 true，则 δ₂ 也 true，与 hne 矛盾）
    by_contra hf
    have h1 : sameAt δ₁ x y = true := by
      cases h : sameAt δ₁ x y
      · exact absurd h hf
      · rfl
    have h2 : sameAt δ₂ x y = true := sameAt_monotone (le_of_lt hlt) h1
    rw [h1, h2] at hne
    exact hne rfl
  · -- sameAt δ₂ 必为 true（由 hne 和上面）
    by_contra ht
    have h2 : sameAt δ₂ x y = false := by
      cases h : sameAt δ₂ x y
      · rfl
      · exact absurd h ht
    have h1f : sameAt δ₁ x y = false := by
      by_contra h1t
      have h1 : sameAt δ₁ x y = true := by
        cases h : sameAt δ₁ x y
        · exact absurd h h1t
        · rfl
      have : sameAt δ₂ x y = true := sameAt_monotone (le_of_lt hlt) h1
      rw [this] at h2
      exact Bool.noConfusion h2
    rw [h1f, h2] at hne
    exact hne rfl

-- 【附范畴】二值相对于上下文：拼接方向确定，排中不绝对。
theorem contextual_binary :
    (∀ {n : ℕ} {x y : StateQuant n} {δ₁ δ₂ : ℚ}, δ₁ ≤ δ₂ →
      sameAt δ₁ x y = true → sameAt δ₂ x y = true) ∧
    (∃ (x y : StateQuant 1) (δ₁ δ₂ : ℚ),
      δ₁ < δ₂ ∧ sameAt δ₁ x y ≠ sameAt δ₂ x y) ∧
    (∃ (x y : StateQuant 1) (δ₁ δ₂ : ℚ), δ₁ < δ₂ ∧
      sameAt δ₁ x y = false ∧ sameAt δ₂ x y = true) :=
  ⟨fun h => sameAt_monotone h, excluded_middle_not_absolute, pieces_depend.2⟩

-- ============ 从附范畴自然导出注意力 ============

/-
  【注意力 = 有多少个上下文认为"同类"】

  附范畴 = 二值 + 上下文。
  每个上下文（层 δ ∈ T）给出一个二值判定 sameAt δ x y：
  这两个元素在层 δ 下是否同类。

  **注意力 = 对这些二值判定的计数**：

      attentionWeight x y T = #{δ ∈ T : sameAt δ x y}

  即：**有多少个上下文认为 x 和 y 是同一个东西。**

  这不是外挂——不需要引入新的结构，只需要把上下文里的二值判定
  聚合起来。注意力是附范畴的**自然读数**。

  三条性质直接给出注意力的直觉：

    · 距离越大，认为同类的上下文越少 → 权重越小；
    · 距离为 0，所有非负上下文都认为同类 → 满权重；
    · 权重有界（≤ |T|）。

  对照 transformer 的 softmax 注意力：

    · softmax 的权重 = exp(similarity) / Σ exp(similarity)；
    · 这里的权重 = #{上下文 : 同类}（线性计数）。

  两者都是"相似度越高，权重越大"，但这里**没有指数、没有归一化常数**——
  它的分母就是上下文的总数，天然归一。
  而且它是**有限的、可暴力枚举的**（v204 的纪律）。

  所以"从附范畴的数字结构自然导出注意力机制"是成立的：
  注意力不是什么神秘的涌现，它是**上下文层上的二值判定的计数**。
-/

-- 注意力权重：有多少个上下文（层）认为 x 和 y 同类。
def attentionWeight {n : ℕ} (x y : StateQuant n) (T : Finset ℚ) : ℕ :=
  (T.filter (fun δ => sameAt δ x y = true)).card

-- 权重有界：不超过上下文的总数。
theorem attentionWeight_le {n : ℕ} (x y : StateQuant n) (T : Finset ℚ) :
    attentionWeight x y T ≤ T.card := by
  unfold attentionWeight
  exact Finset.card_filter_le _ _

-- 【距离越大，注意力越小】权重对距离反单调。
theorem attentionWeight_antitone {n : ℕ} (T : Finset ℚ) {x y x' y' : StateQuant n}
    (h : commonDist x y ≤ commonDist x' y') :
    attentionWeight x' y' T ≤ attentionWeight x y T := by
  unfold attentionWeight
  apply Finset.card_le_card
  intro δ hδ
  simp only [Finset.mem_filter, sameAt, decide_eq_true_iff] at hδ ⊢
  exact ⟨hδ.1, le_trans h hδ.2⟩

-- 【相同 ⟹ 满权重】距离为 0 时，所有非负上下文都认为同类。
theorem attentionWeight_same_full {n : ℕ} (x y : StateQuant n) (T : Finset ℚ)
    (hT : ∀ δ ∈ T, 0 ≤ δ) (h : commonDist x y = 0) :
    attentionWeight x y T = T.card := by
  unfold attentionWeight
  rw [Finset.filter_true_of_mem]
  intro δ hδ
  simp only [sameAt, decide_eq_true_iff]
  rw [h]
  exact hT δ hδ

-- 【注意力来自附范畴】三条合一：有界 + 反单调 + 相同满权重。
theorem attention_from_context :
    (∀ {n : ℕ} (x y : StateQuant n) (T : Finset ℚ),
      attentionWeight x y T ≤ T.card) ∧
    (∀ {n : ℕ} (T : Finset ℚ) {x y x' y' : StateQuant n},
      commonDist x y ≤ commonDist x' y' →
      attentionWeight x' y' T ≤ attentionWeight x y T) ∧
    (∀ {n : ℕ} (x y : StateQuant n) (T : Finset ℚ),
      (∀ δ ∈ T, 0 ≤ δ) → commonDist x y = 0 →
      attentionWeight x y T = T.card) :=
  ⟨fun x y T => attentionWeight_le x y T,
   fun T => attentionWeight_antitone T,
   fun x y T hT h => attentionWeight_same_full x y T hT h⟩

-- ============ 对位 = 有理数：s/r 就是对位类 ============

/-
  【对位就是 x/y，而有理数就是对位类的全体】

  2026-11-13 的底层洞见：
    s、r、n、自我、自反……说到底都是**对位**。
    s 是与别人的间接对位（通过差异场数差异簇），
    r 是直接对位（共享的公共维度面），
    而 s/r 就是一次对位的"面值"。

  数学上：对位 p = x/y。两个对位"相同"的定义是交叉相乘相等：

      (x, y) ∼ (x', y') ⟺ x · y' = x' · y

  这正是 Mathlib 里 ℚ 的定义（整数对按交叉相乘取商）。
  所以：**有理数 = 对位类的全体**。s/r 落在 ℚ 里不是引入连续统，
  而是对位本身的代数：对位的相等是交叉相乘，对位的加是交叉相加，对位的积是相乘。

  这也解释了为什么"守恒（加法）"与"对位（乘除）"能共存于一域：
  ℚ 是同时承载这两件事的有限性场所。
-/

-- 对位：两对读数比值相等（交叉相乘相等）。
def aligned (p q : ℤ × ℕ+) : Prop := p.1 * ((q.2 : ℕ) : ℤ) = q.1 * ((p.2 : ℕ) : ℤ)

theorem aligned_refl (p : ℤ × ℕ+) : aligned p p := by
  unfold aligned
  ring

theorem aligned_symm {p q : ℤ × ℕ+} (h : aligned p q) : aligned q p := by
  unfold aligned at h ⊢
  exact h.symm

theorem aligned_trans {p q r : ℤ × ℕ+} (h1 : aligned p q) (h2 : aligned q r) :
    aligned p r := by
  unfold aligned at h1 h2 ⊢
  have hq : ((q.2 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast q.2.ne_zero
  have key : p.1 * ((r.2 : ℕ) : ℤ) * ((q.2 : ℕ) : ℤ)
      = r.1 * ((p.2 : ℕ) : ℤ) * ((q.2 : ℕ) : ℤ) := by
    calc p.1 * ((r.2 : ℕ) : ℤ) * ((q.2 : ℕ) : ℤ)
        = (p.1 * ((q.2 : ℕ) : ℤ)) * ((r.2 : ℕ) : ℤ) := by ring
      _ = (q.1 * ((p.2 : ℕ) : ℤ)) * ((r.2 : ℕ) : ℤ) := by rw [h1]
      _ = ((p.2 : ℕ) : ℤ) * (q.1 * ((r.2 : ℕ) : ℤ)) := by ring
      _ = ((p.2 : ℕ) : ℤ) * (r.1 * ((q.2 : ℕ) : ℤ)) := by rw [h2]
      _ = r.1 * ((p.2 : ℕ) : ℤ) * ((q.2 : ℕ) : ℤ) := by ring
  exact mul_right_cancel₀ hq key

-- 对位是等价关系（交叉相乘）。
theorem aligned_equivalence : Equivalence aligned :=
  ⟨aligned_refl, aligned_symm, aligned_trans⟩

-- 对位类：对位的全体（= 有理数）。
def alignedSetoid : Setoid (ℤ × ℕ+) := ⟨aligned, aligned_equivalence⟩

abbrev Alignment : Type := Quotient alignedSetoid

-- 对位类 → 有理数：p 的对位值 = p.1 / p.2。
def alignmentToRat : Alignment → ℚ :=
  Quotient.lift (fun p : ℤ × ℕ+ => (p.1 : ℚ) / ((p.2 : ℕ) : ℚ)) (by
    intro p q h
    change aligned p q at h
    unfold aligned at h
    have hp : ((p.2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hq : ((q.2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast q.2.ne_zero
    have h' : (p.1 : ℚ) * ((q.2 : ℕ) : ℚ) = (q.1 : ℚ) * ((p.2 : ℕ) : ℚ) := by
      exact_mod_cast h
    field_simp
    rw [mul_comm (((p.2 : ℕ) : ℚ)) ((q.1 : ℚ))]
    exact h')

-- 有理数 → 对位类：取分子/分母。
def ratToAlignment (q : ℚ) : Alignment :=
  Quotient.mk alignedSetoid (q.num, ⟨q.den, Nat.pos_of_ne_zero q.den_ne_zero⟩)

-- 有理数的分子/分母就是对位的代表元。
theorem alignmentToRat_ratToAlignment (q : ℚ) :
    alignmentToRat (ratToAlignment q) = q := by
  unfold alignmentToRat ratToAlignment
  rw [Quotient.lift_mk]
  simpa using Rat.num_div_den q

-- 对位值的单射：比值相同 ⟹ 交叉相乘相等。
theorem alignmentToRat_injective : Function.Injective alignmentToRat := by
  intro x y
  induction x using Quotient.ind with
  | _ p =>
  induction y using Quotient.ind with
  | _ q =>
    intro h
    have h1 : alignmentToRat (Quotient.mk alignedSetoid p)
        = (p.1 : ℚ) / ((p.2 : ℕ) : ℚ) := by
      unfold alignmentToRat
      rw [Quotient.lift_mk]
    have h2 : alignmentToRat (Quotient.mk alignedSetoid q)
        = (q.1 : ℚ) / ((q.2 : ℕ) : ℚ) := by
      unfold alignmentToRat
      rw [Quotient.lift_mk]
    rw [h1, h2] at h
    have hp : ((p.2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hq : ((q.2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast q.2.ne_zero
    have h' : (p.1 : ℚ) * ((q.2 : ℕ) : ℚ) = (q.1 : ℚ) * ((p.2 : ℕ) : ℚ) := by
      field_simp at h
      rw [mul_comm (((p.2 : ℕ) : ℚ)) ((q.1 : ℚ))] at h
      exact h
    exact Quotient.sound (by
      change aligned p q
      unfold aligned
      exact_mod_cast h')

-- ============ 符号：不是向量，是范畴对象 ============

/-
  【文字即符号：符号数字化为 ℚ，不是 ℝ^d 向量】

  用户的表述（2026-11-15）：
  "里面是一串代数和几何，即文字即符号，符号可以数字化，
  你懂嘛，不是靠向量，而是范畴，不过是附范畴。"

  这直接否定了 transformer 的 embedding 路线：

    · transformer：词 → ℝ^d（向量）→ 内积注意力 → softmax；
    · 这里：      词 → 对位类（ℚ）→ 上下文计数注意力。

  "符号可以数字化" ≠ "符号变成向量"。数字化的意思是：
  符号被映射到一个**有限的、可枚举的**读数——在中枢里就是一个有理数，
  而不是一个 d 维连续向量。

  三个关键区别：

    (1) **维度不是超参数**。transformer 的 d（512 / 768 / 4096）是选的；
        这里每个符号只有**一个** ℚ（对位类），维度由理论固定。
    (2) **关系不是内积**。向量靠点积定义相似度；这里靠**对位相等**
        （交叉相乘），或者靠**上下文计数**（v206）。
    (3) **上下文不是后加的**。向量的"上下文"要靠 attention 学；
        这里的上下文就是**层**（v205），是结构的一部分。

  所以符号不是 ℝ^d 里的点，是**ℚ 上的对位类**——
  这是范畴对象的数字化，不是向量的嵌入。

  代数：符号 = 对位类，有加法（守恒）和乘除（对位）双重结构。
  几何：符号住在一串层上（LayerLadder），每层一个视角。
  而"附"：同一个符号对在不同层上可以"相同"或"不同"（排中不绝对）。
-/

-- 符号 = 对位类（一个 ℚ，不是 d 维向量）。
abbrev Symbol : Type := Alignment

-- 数字化：符号 → ℚ（构造性）。
def Symbol.digit (σ : Symbol) : ℚ := alignmentToRat σ

-- 【一维】每个符号只对应一个有理数，没有超参数的维度。
theorem symbol_dimension_one (σ : Symbol) : ∃ q : ℚ, Symbol.digit σ = q :=
  ⟨_, rfl⟩

-- 【对位而非内积】符号相同 ⟺ 数字化后相等（对位类到 ℚ 是单射）。
theorem symbol_eq_iff_digit_eq (σ τ : Symbol) :
    σ = τ ↔ Symbol.digit σ = Symbol.digit τ := by
  constructor
  · intro h; rw [h]
  · intro h
    exact alignmentToRat_injective h

-- 【打包】符号是范畴对象而不是向量：一维 + 对位相等 + 注意力计数。
theorem symbol_categorical :
    (∀ σ : Symbol, ∃ q : ℚ, Symbol.digit σ = q) ∧
    (∀ σ τ : Symbol, σ = τ ↔ Symbol.digit σ = Symbol.digit τ) ∧
    (∀ {n : ℕ} (x y : StateQuant n) (T : Finset ℚ), attentionWeight x y T =
      (T.filter (fun δ => sameAt δ x y = true)).card) :=
  ⟨fun _ => ⟨_, rfl⟩,
   fun σ τ => symbol_eq_iff_digit_eq σ τ,
   fun _ _ _ => rfl⟩

-- ============ 结构等价于其保护的信息：紧层论 ============

/-
  【一张猫图不能唯一地二分为"猫/非猫"】

  用户的新想法（2026-11-15）：
  "结构等价于其保护的信息……对位，比如一个上面有猫的图片，
  是否可以唯一视作猫和非猫……我的脑子告诉我，不存在一种，
  可能是存在不同的层级，优先处理啥，这里就分层了，
  又出现个层论，不过这里的层论和我的层论更紧，而不是 gro。"

  三件事：

  (1) **对位不是唯一的。** 一张图不只有一种"猫/非猫"的二分；
      每个层 δ 给出一种二分。换一层，二分就变（v205 的排中不绝对）。
      所以对位是一个**族**，不是一个。

  (2) **层级 = 优先级。** 层不是平铺的，是**有序**的：δ 严格递减
      （LayerLadder 的 h_dec）。这个序就是"先处理什么"：
      精细层先看细节，粗糙层后看整体。

  (3) **这里的层论更紧。** Grothendieck 的 site 可以是任意范畴、
      任意覆盖。这里的 site 是**有限一维严格递减的序**（Fin m + ℚ）。
      没有一般的覆盖，只有"下一层"。这就是"更紧"：
      层的位置由 δ 完全决定，层间只有一条路（相邻）。

  而"结构等价于其保护的信息"：

  **一个层的信息 = 它的判定 profile**（它对所有状态对给出的 0/1）。
  两个层"等价" ⟺ 它们的 profile 相同。

  这给出一个精确的事实：**负层不保护任何信息**——
  因为 commonDist ≥ 0 > δ，所有对都判为"不同"（全 false）。
  所以所有负层都等价：它们是"同一层"的不同名字。

  这就是"结构等价于其保护的信息"的第一个定理：
  **层的身份不在 δ，在它保护什么。**
-/

-- commonDist 非负（平方和）。
theorem commonDist_nonneg {m n : ℕ} (x : StateQuant m) (y : StateQuant n) :
    0 ≤ commonDist x y := by
  rw [commonDist_eq_sum_sq]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

-- 层等价：两个层对所有状态对给出相同的判定。
def layerEq (δ₁ δ₂ : ℚ) : Prop :=
  ∀ {n : ℕ} (x y : StateQuant n), sameAt δ₁ x y = sameAt δ₂ x y

-- 【负层无信息】δ < 0 时，所有对都判为"不同"。
theorem negative_layer_informationless {n : ℕ} {δ : ℚ} (hδ : δ < 0)
    (x y : StateQuant n) : sameAt δ x y = false := by
  unfold sameAt
  rw [decide_eq_false_iff_not]
  intro h
  have h0 := commonDist_nonneg x y
  linarith

-- 【结构等价于其保护的信息】所有负层都等价：它们不保护任何信息。
theorem negative_layers_equivalent {δ₁ δ₂ : ℚ} (h₁ : δ₁ < 0) (h₂ : δ₂ < 0) :
    layerEq δ₁ δ₂ :=
  fun x y => by rw [negative_layer_informationless h₁, negative_layer_informationless h₂]

-- 【对位不是唯一的】同一次"猫/非猫"判定，在不同层上不同。
theorem alignment_not_unique :
    ∃ (x y : StateQuant 1) (δ₁ δ₂ : ℚ),
      δ₁ < δ₂ ∧ sameAt δ₁ x y ≠ sameAt δ₂ x y :=
  excluded_middle_not_absolute

-- 【紧层论】层是有序的：δ 严格递减（这正是"优先级"）。
theorem tight_layer_order (L : LayerLadder) :
    ∀ i j : Fin L.m, i < j → L.δ j < L.δ i :=
  fun _ _ h => L.h_dec h

-- 【打包】结构 = 信息 + 对位不唯一 + 紧层序。
theorem structure_is_information :
    -- (1) 负层无信息
    (∀ {n : ℕ} {δ : ℚ}, δ < 0 → ∀ x y : StateQuant n, sameAt δ x y = false) ∧
    -- (2) 负层等价（同一层）
    (∀ {δ₁ δ₂ : ℚ}, δ₁ < 0 → δ₂ < 0 → layerEq δ₁ δ₂) ∧
    -- (3) 对位不是唯一的
    (∃ (x y : StateQuant 1) (δ₁ δ₂ : ℚ),
      δ₁ < δ₂ ∧ sameAt δ₁ x y ≠ sameAt δ₂ x y) :=
  ⟨fun h _ _ => negative_layer_informationless h _ _,
   fun h₁ h₂ => negative_layers_equivalent h₁ h₂,
   alignment_not_unique⟩

-- ============ 保角性管理结构 ============

/-
  【紧层可放射；距离和向量是被管理掉的】

  用户的想法（2026-11-15，续 v208）：

  "紧层可放射，不是拓扑的无穷远点，而是有限远，但是远了，就松了，
   但是依旧有对位，这里就导出了距离，即距离不过是工具，
   即紧的放射保角性。然后我看到你说的'丢失'，我立马想到一个
   石破天惊的想法：保角性管理结构。啥管理失去呢，对，向量和距离！"

  拆成四件事，每件一个定理：

  (1) **放射**：把整个状态沿原点推远。在 ℚ 上就是数乘。
      它是**保角**的——因为它保持所有比值（对位），
      而比值是这里唯一的结构（v207：符号不是向量）。

  (2) **远了就松**：commonDist 按 c² 伸缩。c > 1 时，
      原本在同一层的对被推出这一层。所以层是"紧"的：
      它只收留距离 ≤ δ 的对；推远了，就松了。

  (3) **依旧有对位**：对位（比值）完全不变。层变了，对位没变。
      这就是"紧的放射保角性"。

  (4) **保角性管理结构**：放射把层送到层——
      scaled space 的层 δ 就是原空间的层 δ/c²。
      层族作为一个整体被保角映射**管理**（重标），不被破坏。

  而**被管理掉的是距离和向量**：

  - 距离：保角下不是不变量（`distance_not_invariant`）——它是工具，不是本质；
  - 向量：整个论证只用了标量乘积，没有点积、没有范数（v207）。

  至于"不是拓扑的无穷远点，而是有限远"：

  **ℚ 里没有无穷远点**。放射的每一步 c 都是一个有限的 ℚ；但把 c 取遍，
  射线能超过任何一层（`ray_eventually_different`）。
  有限远，无终点，但松到无界——这就是"潜无穷"，
  正是 θ 拒绝实无穷（拒 ℝ）的同一个姿态。
-/

-- 放射：沿原点伸缩（c > 0 是把整个空间推远）。
def scale {n : ℕ} (c : ℚ) (x : StateQuant n) : StateQuant n :=
  { val := fun i => c * x.val i, phase := x.phase }

-- 比值相同：a/b = a'/b' 的交叉相乘形式（不需要除法，也不需要距离）。
def ratioEq (a b a' b' : ℚ) : Prop := a * b' = a' * b

-- 两边同乘 c 后交叉相乘相等 ⟺ 原来相等（c ≠ 0）。
theorem ratioEq_scale_cancel {a b d e c : ℚ} (hc : c ≠ 0) :
    (c * a) * (c * d) = (c * b) * (c * e) ↔ a * d = b * e := by
  constructor
  · intro h2
    have h3 : c ^ 2 * (a * d) = c ^ 2 * (b * e) := by
      calc c ^ 2 * (a * d) = (c * a) * (c * d) := by ring
        _ = (c * b) * (c * e) := h2
        _ = c ^ 2 * (b * e) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hc) h3
  · intro h2
    calc (c * a) * (c * d) = c ^ 2 * (a * d) := by ring
      _ = c ^ 2 * (b * e) := by rw [h2]
      _ = (c * b) * (c * e) := by ring

-- (1) 【保角 = 保对位】放射保持一切比值，只需要标量的乘积。
theorem scale_preserves_ratio {n : ℕ} (c : ℚ) (hc : c ≠ 0)
    (x y : StateQuant n) (i j : Fin n) :
    ratioEq (x.val i) (x.val j) (y.val i) (y.val j) ↔
    ratioEq ((scale c x).val i) ((scale c x).val j) ((scale c y).val i) ((scale c y).val j) := by
  dsimp [ratioEq, scale]
  exact (ratioEq_scale_cancel hc).symm

-- (2) 【距离被管理】放射按 c² 改变距离：距离不是保角不变量。
theorem scale_commonDist {n : ℕ} (c : ℚ) (x y : StateQuant n) :
    commonDist (scale c x) (scale c y) = c ^ 2 * commonDist x y := by
  unfold commonDist scale
  simp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

-- ============ 计算网格：b₁ 度量扩张 ============

-- 收缩层平坦（|c| ≤ 1）。
theorem squareFlat_scale_of_le {n : ℕ} {c δ : ℚ} (hc : c ^ 2 ≤ 1) :
    SquareFlat (n := n) δ (scale (n := n) c) := by
  intro x y hxy
  rw [scale_commonDist]
  have hD : 0 ≤ commonDist x y := commonDist_nonneg x y
  nlinarith

-- 【核心】δ = 1 时，scale c 平坦 ⟺ c² ≤ 1（扩张才破方格）。
theorem squareFlat_scale_one (c : ℚ) :
    SquareFlat (n := 1) 1 (scale (n := 1) c) ↔ c ^ 2 ≤ 1 := by
  constructor
  · intro h
    have h' := h ⟨fun _ => 0, .neutral⟩ ⟨fun _ => 1, .neutral⟩ (by
      rw [commonDist_one]; norm_num)
    rw [commonDist_one] at h'
    have hv1 : (scale (n := 1) c (⟨fun _ : Fin 1 => (0:ℚ), .neutral⟩ : StateQuant 1)).val 0 = 0 := by
      simp [scale]
    have hv2 : (scale (n := 1) c (⟨fun _ : Fin 1 => (1:ℚ), .neutral⟩ : StateQuant 1)).val 0 = c := by
      simp [scale]
    rw [hv1, hv2] at h'
    have hsq : ((0 : ℚ) - c) ^ 2 = c ^ 2 := by ring
    rwa [hsq] at h'
  · intro hc
    exact squareFlat_scale_of_le hc

-- 【打包】计算网格的 b₁：收缩层自动平坦，扩张层才产生环。
theorem computation_grid_b1 :
    -- (1) 恒等层平坦
    (∀ (n : ℕ) (δ : ℚ), SquareFlat δ (id : StateQuant n → StateQuant n)) ∧
    -- (2) 平坦在复合下保持
    (∀ {n : ℕ} {δ : ℚ} {T₁ T₂ : StateQuant n → StateQuant n},
      SquareFlat δ T₁ → SquareFlat δ T₂ → SquareFlat δ (T₂ ∘ T₁)) ∧
    -- (3) 收缩层平坦
    (∀ {n : ℕ} {c δ : ℚ}, c ^ 2 ≤ 1 → SquareFlat (n := n) δ (scale (n := n) c)) ∧
    -- (4) 【核心】δ = 1 时平坦 ⟺ 不扩张
    (∀ c : ℚ, SquareFlat (n := 1) 1 (scale (n := 1) c) ↔ c ^ 2 ≤ 1) ∧
    -- (5) ReLU 层平坦（1-Lipschitz）
    (∀ δ : ℚ, SquareFlat (n := 1) δ (reluState)) ∧
    -- (6) 每有一个不平坦的方格，b₁ 加一
    (∀ n cuts : ℤ,
      eulerB1 (n * n) (2 * n * (n - 1)) ((n - 1) * (n - 1) - cuts) = cuts) :=
  ⟨fun _ δ => squareFlat_id δ,
   fun h₁ h₂ => squareFlat_comp h₁ h₂,
   fun hc => squareFlat_scale_of_le hc,
   fun c => squareFlat_scale_one c,
   fun δ => squareFlat_relu δ,
   fun n cuts => euler_b1_cuts n cuts⟩

theorem distance_not_invariant {n : ℕ} {c : ℚ} (hc : 1 < c)
    (x y : StateQuant n) (hpos : 0 < commonDist x y) :
    commonDist (scale c x) (scale c y) ≠ commonDist x y := by
  rw [scale_commonDist]
  intro h
  have hc2 : (1 : ℚ) < c ^ 2 := by nlinarith
  have hp : 0 < (c ^ 2 - 1) * commonDist x y := mul_pos (by linarith) hpos
  nlinarith

-- (3) 【保角性管理结构】放射把层送到层：scaled 的层 δ 就是原来的层 δ/c²。
theorem scale_layer_iff {n : ℕ} (c : ℚ) (hc : 0 < c) (δ : ℚ) (x y : StateQuant n) :
    commonDist (scale c x) (scale c y) ≤ δ ↔ commonDist x y ≤ δ / c ^ 2 := by
  rw [scale_commonDist]
  have hc2 : (0 : ℚ) < c ^ 2 := by positivity
  rw [le_div_iff₀ hc2, mul_comm (commonDist x y)]

theorem scale_acts_on_layers {n : ℕ} (c : ℚ) (hc : 0 < c) (δ : ℚ) (x y : StateQuant n) :
    sameAt δ (scale c x) (scale c y) = sameAt (δ / c ^ 2) x y := by
  have h := scale_layer_iff c hc δ x y
  unfold sameAt
  by_cases hb : commonDist (scale c x) (scale c y) ≤ δ
  · have hb2 : commonDist x y ≤ δ / c ^ 2 := h.mp hb
    rw [decide_eq_true_eq.mpr hb, decide_eq_true_eq.mpr hb2]
  · have hb2 : ¬ commonDist x y ≤ δ / c ^ 2 := fun hx => hb (h.mpr hx)
    rw [decide_eq_false_iff_not.mpr hb, decide_eq_false_iff_not.mpr hb2]

-- (4) 【有限远，无终点】ℚ 里没有无穷远点：每一步都有限，但射线能超过任何层。
theorem rat_sq_unbounded {D : ℚ} (hD : 0 < D) (δ : ℚ) :
    ∃ c : ℚ, 1 < c ∧ δ < c ^ 2 * D := by
  refine ⟨|(δ + 1) / D| + 2, ?_, ?_⟩
  · have h := abs_nonneg ((δ + 1) / D); linarith
  · have hc1 : (1 : ℚ) < |(δ + 1) / D| + 2 := by
      have h := abs_nonneg ((δ + 1) / D); linarith
    have hlt : (δ + 1) / D < |(δ + 1) / D| + 2 := by
      have h := le_abs_self ((δ + 1) / D); linarith
    have hmul : (δ + 1) / D * D < (|(δ + 1) / D| + 2) * D :=
      mul_lt_mul_of_pos_right hlt hD
    have hq : (δ + 1) / D * D = δ + 1 := by field_simp
    have hsq : (|(δ + 1) / D| + 2) ≤ (|(δ + 1) / D| + 2) ^ 2 := by nlinarith [hc1]
    have hle := mul_le_mul_of_nonneg_right hsq (le_of_lt hD)
    linarith

theorem ray_eventually_different {n : ℕ} {δ : ℚ} (x y : StateQuant n)
    (hpos : 0 < commonDist x y) :
    ∃ c : ℚ, 1 < c ∧ δ < commonDist (scale c x) (scale c y) := by
  obtain ⟨c, hc1, hcδ⟩ := rat_sq_unbounded hpos δ
  exact ⟨c, hc1, by rw [scale_commonDist]; exact hcδ⟩

-- 【打包】保角性管理结构：保对位 + 距离被管理 + 层族封闭 + 射线逃逸但每步有限。
theorem conformal_manages_structure :
    -- (1) 保角 = 保对位
    (∀ {n : ℕ} (c : ℚ), c ≠ 0 → ∀ (x y : StateQuant n) (i j : Fin n),
      (ratioEq (x.val i) (x.val j) (y.val i) (y.val j) ↔
       ratioEq ((scale c x).val i) ((scale c x).val j)
              ((scale c y).val i) ((scale c y).val j))) ∧
    -- (2) 距离被管理（不是不变量）
    (∀ {n : ℕ} {c : ℚ}, 1 < c → ∀ (x y : StateQuant n), 0 < commonDist x y →
      commonDist (scale c x) (scale c y) ≠ commonDist x y) ∧
    -- (3) 层族在放射下封闭（只是重标）
    (∀ {n : ℕ} (c : ℚ), 0 < c → ∀ (δ : ℚ) (x y : StateQuant n),
      sameAt δ (scale c x) (scale c y) = sameAt (δ / c ^ 2) x y) ∧
    -- (4) 有限远但无终点：射线能超过任何层
    (∀ {n : ℕ} (x y : StateQuant n) (δ : ℚ), 0 < commonDist x y →
      ∃ c : ℚ, 1 < c ∧ δ < commonDist (scale c x) (scale c y)) :=
  ⟨fun c hc _ _ _ _ => scale_preserves_ratio c hc _ _ _ _,
   fun hc _ _ hpos => distance_not_invariant hc _ _ hpos,
   fun c hc δ x y => scale_acts_on_layers c hc δ x y,
   fun x y _ hpos => ray_eventually_different x y hpos⟩

-- ============ 保角群作用的完全分解 ============

/-
  【保角群 = ℚ^×；它在重要的东西上恒等，在不重要的东西上翻搅】

  v209 说"保角性管理结构"。v210 问：管理它的到底是谁？

  保角 = 保比值。而保比值的变换只能数乘（平移破坏比值）。
  所以保角群就是 ℚ^×（乘法群）。它对 StateQuant 的作用是 `scale c`。

  于是整个作用可以**完全分解**成三层：

  (1) **不变量层（群作用平凡）**：对位。数乘不改变任何比值——
      (c·a)/(c·b) = a/b。群在"重要的东西"上什么都没动。

  (2) **轨道层（群作用非平凡但可算）**：两个状态在同一轨道
      ⟺ 只差一个非零标量。轨道是一个等价关系（`scale_orbit_equivalence`）。

  (3) **商层**：轨道空间由比值完全决定——两个二维非零态同轨道
      ⟺ 它们的比值相同（`orbit_iff_ratio`）。所以

          **商 ≅ ℚ**（就是 v207 的对位层）

  而层编号 δ 也被这个群搬动（v209：δ ↦ δ/c²），距离按 c² 变。

  这就是"管理"的代数定义：**一个群作用，对不变量恒等，
  对轨道翻搅，商完全可算。** v196 的不可分解性在这里不出现，
  因为 ℚ^× 是交换群、在 ℚ 上可对角化——这正是"能分解"的来源。
-/

-- 群公理：单位元。
theorem scale_one {n : ℕ} (x : StateQuant n) : scale 1 x = x := by
  unfold scale
  simp

-- 群公理：复合 = 相乘。
theorem scale_mul {n : ℕ} (c d : ℚ) (x : StateQuant n) :
    scale c (scale d x) = scale (c * d) x := by
  unfold scale
  simp only [StateQuant.mk.injEq]
  exact ⟨funext (fun i => by ring), trivial⟩

-- 群公理：c ≠ 0 时作用可逆（单射）。
theorem scale_injective {n : ℕ} (c : ℚ) (hc : c ≠ 0) :
    Function.Injective (scale (n := n) c) := by
  intro x y h
  obtain ⟨xv, xp⟩ := x
  obtain ⟨yv, yp⟩ := y
  simp only [scale, StateQuant.mk.injEq] at h
  obtain ⟨hv, hp⟩ := h
  simp only [StateQuant.mk.injEq]
  exact ⟨funext (fun i => mul_left_cancel₀ hc (by simpa using congrFun hv i)), hp⟩

-- 【不变量层】群作用在对位上平凡：(c·a)/(c·b) = a/b。
theorem div_scale_cancel {a b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0) :
    (c * a) / (c * b) = a / b := by
  field_simp

-- 0 不在群里：它把一切压成原点（这是作用唯一的坍缩点）。
theorem scale_zero_collapse {n : ℕ} (x : StateQuant n) (i : Fin n) :
    (scale 0 x).val i = 0 := by
  simp [scale]

-- 【轨道层】同轨道是一个等价关系。
theorem scale_orbit_equivalence (n : ℕ) :
    Equivalence (fun x y : StateQuant n => ∃ c : ℚ, c ≠ 0 ∧ y = scale c x) where
  refl x := ⟨1, one_ne_zero, by rw [scale_one]⟩
  symm := by
    rintro x y ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [scale_mul, inv_mul_cancel₀ hc, scale_one]⟩
  trans := by
    rintro x y z ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨d * c, mul_ne_zero hd hc, by rw [scale_mul]⟩

-- 【商层 = 对位层】二维非零态同轨道 ⟺ 比值相同 ⟺ 相角相同。
theorem orbit_iff_ratio {x y : StateQuant 2} (hx : x.val 0 ≠ 0) (hy : y.val 0 ≠ 0) :
    (∃ c : ℚ, c ≠ 0 ∧ y = scale c x) ↔
      (y.val 1 / y.val 0 = x.val 1 / x.val 0 ∧ y.phase = x.phase) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨div_scale_cancel hx hc, rfl⟩
  · rintro ⟨hr, hp⟩
    obtain ⟨yv, yp⟩ := y
    obtain ⟨xv, xp⟩ := x
    refine ⟨yv 0 / xv 0, div_ne_zero hy hx, ?_⟩
    have hr' : yv 1 * xv 0 = xv 1 * yv 0 := by
      field_simp at hr
      linarith
    have h0 : (yv 0 / xv 0) * xv 0 = yv 0 := by field_simp
    have h1 : (yv 0 / xv 0) * xv 1 = yv 1 := by
      field_simp
      linarith
    simp only [scale, StateQuant.mk.injEq]
    exact ⟨funext (fun i => by
        fin_cases i
        · exact h0.symm
        · exact h1.symm), hp⟩

-- 【打包】保角群作用的完全分解：群公理 + 不变量层 + 轨道层 + 商 = ℚ。
theorem conformal_action_trichotomy :
    -- (1) 群公理：单位、复合、可逆
    (∀ {n : ℕ} (x : StateQuant n), scale 1 x = x) ∧
    (∀ {n : ℕ} (c d : ℚ) (x : StateQuant n), scale c (scale d x) = scale (c * d) x) ∧
    (∀ {n : ℕ} (c : ℚ), c ≠ 0 → Function.Injective (scale (n := n) c)) ∧
    -- (2) 不变量层：群在对位上平凡
    (∀ {a b c : ℚ}, b ≠ 0 → c ≠ 0 → (c * a) / (c * b) = a / b) ∧
    -- (3) 轨道层：等价关系
    (∀ n : ℕ, Equivalence (fun x y : StateQuant n => ∃ c : ℚ, c ≠ 0 ∧ y = scale c x)) ∧
    -- (4) 商层：二维非零态同轨道 ⟺ 比值相同（商 ≅ ℚ）
    (∀ {x y : StateQuant 2}, x.val 0 ≠ 0 → y.val 0 ≠ 0 →
      ((∃ c : ℚ, c ≠ 0 ∧ y = scale c x) ↔
        (y.val 1 / y.val 0 = x.val 1 / x.val 0 ∧ y.phase = x.phase))) :=
  ⟨fun _ => scale_one _,
   fun c d _ => scale_mul c d _,
   fun c hc => scale_injective c hc,
   fun hb hc => div_scale_cancel hb hc,
   fun n => scale_orbit_equivalence n,
   fun hx hy => orbit_iff_ratio hx hy⟩

-- ============ 双重作用：ℚ^× × ℤ/2 ============

/-
  【谁管相位？严格可分吗？】

  v210 说：ℚ^× 管对位和距离。但 `orbit_iff_ratio` 的结论是
  "比值相同 ∧ 相角相同"——相位不在 ℚ^× 的商里，它站着不动。

  相位是 v164–v166 的老朋友：phase_card = 3，正/负/中性。
  管它的是另一个群：**ℤ/2（半转）**。

  问题：ℚ^× 和 ℤ/2 是**直积（可分）**，还是有**耦合（不可分）**？

  答案：**完全直积**。理由一句话——

      StateQuant 有两个正交坐标：val（量）和 phase（符号）。
      ℚ^× 只动 val，ℤ/2 只动 phase，两个作用对易。

  所以 v196 的不可分解性在这里不出现：耦合项恒等于零。
  这不是运气，是设计——差异论把"多少"和"什么号"从一开始
  就摆在两个不同的坐标上。**可分性是坐标系的产物。**

  收口：v204 的 `Phase.bit`（附范畴的底层位）正好就是
  **ℤ/2 的商映射**。二值是相位轨道的名字，不是外加的标签。
-/

-- 半转：正负互换，中性不动。ℤ/2 在 Phase 上的作用。
def flipPhase : Phase → Phase
  | .positive => .negative
  | .negative => .positive
  | .neutral  => .neutral

-- ℤ/2 公理：翻两次回来。
theorem flipPhase_involutive : ∀ p : Phase, flipPhase (flipPhase p) = p
  | .positive => rfl
  | .negative => rfl
  | .neutral  => rfl

-- 半转 = 符号取反。
theorem phaseSign_flipPhase (p : Phase) : phaseSign (flipPhase p) = - phaseSign p := by
  cases p <;> simp [flipPhase, phaseSign]

-- 中性是唯一的不动点。
theorem flipPhase_fixed_iff (p : Phase) : flipPhase p = p ↔ p = .neutral := by
  cases p <;> simp [flipPhase]

-- 半转是单射（作用可逆）。
theorem flipPhase_injective : Function.Injective flipPhase :=
  fun _ _ h => by
    have := congrArg flipPhase h
    simpa [flipPhase_involutive] using this

-- 作用在 StateQuant 上：只动相位，不动量。
def flipState {n : ℕ} (x : StateQuant n) : StateQuant n :=
  { val := x.val, phase := flipPhase x.phase }

theorem flipState_involutive {n : ℕ} (x : StateQuant n) :
    flipState (flipState x) = x := by
  obtain ⟨xv, xp⟩ := x
  simp only [flipState, StateQuant.mk.injEq]
  exact ⟨trivial, flipPhase_involutive xp⟩


-- 【正交性 1】半转不动距离：相位不参与量。
theorem flipState_commonDist {n : ℕ} (x y : StateQuant n) :
    commonDist (flipState x) (flipState y) = commonDist x y := rfl

-- 【正交性 2】半转不动层判定。
theorem flipState_sameAt {n : ℕ} (δ : ℚ) (x y : StateQuant n) :
    sameAt δ (flipState x) (flipState y) = sameAt δ x y := by
  unfold sameAt
  rw [flipState_commonDist]

-- 【对易】两个作用互相不认识。
theorem flipState_scale_comm {n : ℕ} (c : ℚ) (x : StateQuant n) :
    flipState (scale c x) = scale c (flipState x) := rfl

-- 直积作用：ℚ^× × ℤ/2 同时作用。
def actPair {n : ℕ} (c : ℚ) (b : Bool) (x : StateQuant n) : StateQuant n :=
  { val := fun i => c * x.val i, phase := if b then flipPhase x.phase else x.phase }

theorem actPair_one {n : ℕ} (x : StateQuant n) : actPair 1 false x = x := by
  obtain ⟨xv, xp⟩ := x
  simp [actPair]

-- 【量只依赖 c】距离与相位位 b 无关。
theorem actPair_commonDist {n : ℕ} (c : ℚ) (b b' : Bool) (x y : StateQuant n) :
    commonDist (actPair c b x) (actPair c b' y) = c ^ 2 * commonDist x y := by
  unfold commonDist actPair
  simp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

-- 【相位只依赖 b】相位与标量 c 无关。
theorem actPair_phase_eq {n : ℕ} (c c' : ℚ) (b : Bool) (x : StateQuant n) :
    (actPair c b x).phase = (actPair c' b x).phase := by
  simp [actPair]

-- 【直积分解】组合作用 = 两个作用的复合。
theorem actPair_decomposes {n : ℕ} (c : ℚ) (b : Bool) (x : StateQuant n) :
    actPair c b x = (if b then flipState (scale c x) else scale c x) := by
  obtain ⟨xv, xp⟩ := x
  cases b
  · simp [actPair, scale]
  · simp [actPair, flipState, scale]

theorem scale_eq_actPair_false {n : ℕ} (c : ℚ) (x : StateQuant n) :
    scale c x = actPair c false x := by
  obtain ⟨xv, xp⟩ := x
  simp [scale, actPair]

theorem flipScale_eq_actPair_true {n : ℕ} (c : ℚ) (x : StateQuant n) :
    flipState (scale c x) = actPair c true x := by
  obtain ⟨xv, xp⟩ := x
  simp [scale, actPair, flipState]

-- 【收口 v204】附范畴的底层位 = ℤ/2 的商映射。
theorem bit_eq_iff_same_orbit {p q : Phase} :
    Phase.bit p = Phase.bit q ↔ (p = q ∨ q = flipPhase p) := by
  cases p <;> cases q <;> simp [Phase.bit, flipPhase]

-- 【商 = ℚ × 2】组合作用的轨道由 (比值, 相位轨道) 完全决定。
theorem orbit_pair_classified {x y : StateQuant 2} (hx : x.val 0 ≠ 0) (hy : y.val 0 ≠ 0) :
    (∃ (c : ℚ) (b : Bool), c ≠ 0 ∧ y = actPair c b x) ↔
      (y.val 1 / y.val 0 = x.val 1 / x.val 0 ∧
        (y.phase = x.phase ∨ y.phase = flipPhase x.phase)) := by
  constructor
  · rintro ⟨c, b, hc, rfl⟩
    cases b
    · refine ⟨?_, ?_⟩
      · exact div_scale_cancel hx hc
      · simp [actPair]
    · refine ⟨?_, ?_⟩
      · exact div_scale_cancel hx hc
      · simp [actPair]
  · rintro ⟨hr, hp | hp⟩
    · obtain ⟨c, hc, hz⟩ := (orbit_iff_ratio hx hy).mpr ⟨hr, hp⟩
      exact ⟨c, false, hc, by rw [← scale_eq_actPair_false]; exact hz⟩
    · have hp' : flipPhase y.phase = x.phase := by rw [hp, flipPhase_involutive]
      obtain ⟨c, hc, hz⟩ := (orbit_iff_ratio (x := x) (y := flipState y) hx hy).mpr ⟨hr, hp'⟩
      refine ⟨c, true, hc, ?_⟩
      rw [← flipScale_eq_actPair_true]
      calc y = flipState (flipState y) := (flipState_involutive y).symm
        _ = flipState (scale c x) := by rw [hz]

-- 【打包】双重作用完全分解：两个群各管一个坐标，互不干涉，商 = ℚ × (ℤ/2-轨道)。
theorem product_action_decomposes :
    -- (1) ℤ/2 公理
    (∀ p : Phase, flipPhase (flipPhase p) = p) ∧
    -- (2) 相位不动距离（正交性 1）
    (∀ {n : ℕ} (x y : StateQuant n),
      commonDist (flipState x) (flipState y) = commonDist x y) ∧
    -- (3) 相位不动层（正交性 2）
    (∀ {n : ℕ} (δ : ℚ) (x y : StateQuant n),
      sameAt δ (flipState x) (flipState y) = sameAt δ x y) ∧
    -- (4) 两个作用对易
    (∀ {n : ℕ} (c : ℚ) (x : StateQuant n),
      flipState (scale c x) = scale c (flipState x)) ∧
    -- (5) 量只依赖 c（与 b 无关）
    (∀ {n : ℕ} (c : ℚ) (b b' : Bool) (x y : StateQuant n),
      commonDist (actPair c b x) (actPair c b' y) = c ^ 2 * commonDist x y) ∧
    -- (6) 相位只依赖 b（与 c 无关）
    (∀ {n : ℕ} (c c' : ℚ) (b : Bool) (x : StateQuant n),
      (actPair c b x).phase = (actPair c' b x).phase) ∧
    -- (7) 直积分解
    (∀ {n : ℕ} (c : ℚ) (b : Bool) (x : StateQuant n),
      actPair c b x = (if b then flipState (scale c x) else scale c x)) ∧
    -- (8) 相位商 = 附范畴的底层位
    (∀ p q : Phase, Phase.bit p = Phase.bit q ↔ (p = q ∨ q = flipPhase p)) ∧
    -- (9) 商 = ℚ × 2
    (∀ {x y : StateQuant 2}, x.val 0 ≠ 0 → y.val 0 ≠ 0 →
      ((∃ (c : ℚ) (b : Bool), c ≠ 0 ∧ y = actPair c b x) ↔
        (y.val 1 / y.val 0 = x.val 1 / x.val 0 ∧
          (y.phase = x.phase ∨ y.phase = flipPhase x.phase)))) :=
  ⟨flipPhase_involutive,
   fun _ _ => flipState_commonDist _ _,
   fun δ _ _ => flipState_sameAt δ _ _,
   fun c _ => flipState_scale_comm c _,
   fun c _ _ _ _ => actPair_commonDist c _ _ _ _,
   fun c c' b _ => actPair_phase_eq c c' b _,
   fun c b _ => actPair_decomposes c b _,
   fun _ _ => bit_eq_iff_same_orbit,
   fun hx hy => orbit_pair_classified hx hy⟩

-- ============ 坐标唯一性 ============

/-
  【为什么非得是 val / phase 这对坐标？】

  v211 说：ℚ^× 管 val，ℤ/2 管 phase，两个作用对易，所以可分。
  但这是**事后**的话——是坐标恰好这样分，才这样可分的吗？

  唯一性要说的正是：**这对坐标不是可选的之一，是唯一的那个。**

  六条，层层收紧：

  (1) **完备**：两个投影联合起来决定一切。没有一个状态漏网。

  (2) **都必需**：单独任何一个都不够。
      - val 相同、phase 不同 → 是两个不同的态；
      - phase 相同、val 不同 → 也是两个不同的态。
      删掉任何一个坐标，信息就丢了。

  (3) **作用矩阵严格对角**：
      ```
                 val        phase
      ℚ^×      非平凡       平凡
      ℤ/2       平凡       非平凡
      ```
      每一格都是"非平凡"的**见证**或"平凡"的**全称命题**，
      不是比喻。没有交叉项——这就是可分性的全部内容。

  (4) **忠实**：每个群在自己的坐标上是忠实的。
      - ℚ^×：只有 c = 1 才不动非零态；
      - ℤ/2：只有中性才不动。
      没有群在偷懒。

  (5) **不可再分**：ℤ/2-不变的函数**分不开正与负**。
      {+, −} 是单个轨道——这是相位坐标的下界，
      再往下切就没有群论根据了。

  (6) **一维时只剩相位**：一维非零态、同相位的，全在同一轨道。
      ℚ^× 完全齐次（transitive），所以除了相位只剩一个点。
      这就是"val 坐标被 ℚ^× 完全消耗掉"的意思。

  六条合起来：**两个坐标，各自被自己的群完全刻画，互不侵入，
  且缺一不可。** 这不是选了组好坐标，是坐标被群作用逼出来。
-/

-- (1) 【完备】两坐标联合单射。
theorem val_phase_complete {n : ℕ} {x y : StateQuant n}
    (h1 : x.val = y.val) (h2 : x.phase = y.phase) : x = y := by
  obtain ⟨xv, xp⟩ := x
  obtain ⟨yv, yp⟩ := y
  simp only [StateQuant.mk.injEq] at h1 h2 ⊢
  exact ⟨h1, h2⟩

-- (2a) 【val 不充分】val 相同但 phase 不同。
theorem val_not_sufficient :
    ∃ (x y : StateQuant 1), x.val = y.val ∧ x.phase ≠ y.phase :=
  ⟨⟨fun _ => 0, .positive⟩, ⟨fun _ => 0, .negative⟩, rfl, by simp⟩

-- (2b) 【phase 不充分】phase 相同但 val 不同。
theorem phase_not_sufficient :
    ∃ (x y : StateQuant 1), x.phase = y.phase ∧ x.val ≠ y.val :=
  ⟨⟨fun _ => 0, .neutral⟩, ⟨fun _ => 1, .neutral⟩, rfl, by
    intro h
    simpa using congrFun h 0⟩

-- (3a) ℚ^× 在 phase 上严格平凡。
theorem scale_phase_trivial {n : ℕ} (c : ℚ) (x : StateQuant n) :
    (scale c x).phase = x.phase := rfl

-- (3b) ℤ/2 在 val 上严格平凡。
theorem flip_val_trivial {n : ℕ} (x : StateQuant n) : (flipState x).val = x.val := rfl

-- (3c) ℚ^× 在 val 上确实非平凡（见证）。
theorem scale_val_nontrivial :
    ∃ (c : ℚ) (x : StateQuant 1), c ≠ 0 ∧ (scale c x).val ≠ x.val :=
  ⟨2, ⟨fun _ => 1, .neutral⟩, by norm_num, by
    intro h
    have h' : (2 : ℚ) * 1 = 1 := congrFun h 0
    norm_num at h'⟩

-- (3d) ℤ/2 在 phase 上确实非平凡（见证）。
theorem flip_phase_nontrivial :
    ∃ (x : StateQuant 1), (flipState x).phase ≠ x.phase :=
  ⟨⟨fun _ => 0, .positive⟩, by simp [flipState, flipPhase]⟩

-- (4a) 【忠实】ℚ^× 只有 c = 1 才不动非零态。
theorem scale_faithful {n : ℕ} {x : StateQuant n} {i : Fin n} (hi : x.val i ≠ 0)
    {c : ℚ} (h : scale c x = x) : c = 1 := by
  have h' : c * x.val i = x.val i := by
    have := congrArg (fun z => z.val i) h
    simpa [scale] using this
  exact mul_right_cancel₀ hi (by rw [one_mul]; exact h')

-- (4b) 【忠实】ℤ/2 只有中性才不动。
theorem flip_faithful {n : ℕ} (x : StateQuant n) (h : flipState x = x) :
    x.phase = .neutral := by
  have h' : flipPhase x.phase = x.phase := by
    have := congrArg (fun z => z.phase) h
    simpa [flipState] using this
  exact (flipPhase_fixed_iff x.phase).mp h'

-- (5) 【不可再分】ℤ/2-不变的函数分不开正与负。
theorem no_sign_refinement {β : Type*} (f : Phase → β)
    (hf : ∀ p, f (flipPhase p) = f p) : f .positive = f .negative := by
  have h := hf .positive
  rw [show flipPhase .positive = .negative from rfl] at h
  exact h.symm

-- (6) 【一维齐次】一维非零态、同相位 ⟹ 同一轨道（ℚ^× 完全消耗 val）。
theorem one_dim_one_orbit {x y : StateQuant 1} (hx : x.val 0 ≠ 0) (hy : y.val 0 ≠ 0)
    (hp : x.phase = y.phase) :
    ∃ c : ℚ, c ≠ 0 ∧ y = scale c x := by
  obtain ⟨xv, xp⟩ := x
  obtain ⟨yv, yp⟩ := y
  have hp' : yp = xp := hp.symm
  refine ⟨yv 0 / xv 0, div_ne_zero hy hx, ?_⟩
  simp only [scale, StateQuant.mk.injEq]
  refine ⟨?_, hp'⟩
  funext i
  have hi0 : i = 0 := Subsingleton.elim i 0
  rw [hi0]
  field_simp

-- 【打包】坐标唯一性：完备 + 都必需 + 严格对角 + 忠实 + 不可再分 + 一维齐次。
theorem coordinates_unique :
    -- (1) 完备
    (∀ {n : ℕ} {x y : StateQuant n}, x.val = y.val → x.phase = y.phase → x = y) ∧
    -- (2) 都必需
    (∃ (x y : StateQuant 1), x.val = y.val ∧ x.phase ≠ y.phase) ∧
    (∃ (x y : StateQuant 1), x.phase = y.phase ∧ x.val ≠ y.val) ∧
    -- (3) 严格对角
    (∀ {n : ℕ} (c : ℚ) (x : StateQuant n), (scale c x).phase = x.phase) ∧
    (∀ {n : ℕ} (x : StateQuant n), (flipState x).val = x.val) ∧
    (∃ (c : ℚ) (x : StateQuant 1), c ≠ 0 ∧ (scale c x).val ≠ x.val) ∧
    (∃ (x : StateQuant 1), (flipState x).phase ≠ x.phase) ∧
    -- (4) 忠实
    (∀ {n : ℕ} {x : StateQuant n} {i : Fin n}, x.val i ≠ 0 → ∀ {c : ℚ},
      scale c x = x → c = 1) ∧
    (∀ {n : ℕ} (x : StateQuant n), flipState x = x → x.phase = .neutral) ∧
    -- (5) 不可再分
    (∀ {β : Type*} (f : Phase → β), (∀ p, f (flipPhase p) = f p) →
      f .positive = f .negative) ∧
    -- (6) 一维齐次
    (∀ {x y : StateQuant 1}, x.val 0 ≠ 0 → y.val 0 ≠ 0 → x.phase = y.phase →
      ∃ c : ℚ, c ≠ 0 ∧ y = scale c x) :=
  ⟨val_phase_complete,
   val_not_sufficient,
   phase_not_sufficient,
   scale_phase_trivial,
   flip_val_trivial,
   scale_val_nontrivial,
   flip_phase_nontrivial,
   scale_faithful,
   flip_faithful,
   no_sign_refinement,
   one_dim_one_orbit⟩

-- ============ 每层一个范畴 ============

/-
  【附范畴结构的第①项：每层一个范畴】

  对象 = 凝结对象（ResLayer.object：同层等价的商）；
  态射 = 保持凝结的映射（把同层的态仍送到同层的态）。

  这样每层 δ 就是一个真正的范畴：有对象、有态射、有恒等、
  有复合、有结合律。而且态射可以**压到商上**，作用在真正的
  凝结对象上（不只是 StateQuant）。

  层与层之间有**函子**：消解 ℛ_D（v174 的 resolution_id / resolution_comp
  已经证明了函子律）。这是"更紧的层论"在范畴层面的话：
  不是任意 site，是一条 (Fin m, ≤) 上的链。

  符号在这里的位置：**符号住在某一层里**。它是对位类，
  而对位类是这一层的对象之间的读数——所以"符号代数"
  就是"层范畴的读数代数"。
-/

-- 层范畴的态射：把同层的态送到同层的态。
structure LayerHom (L : ResLayer) (n : ℕ) where
  toFun : StateQuant n → StateQuant n
  resp : ∀ x y : StateQuant n, ResLayer.related L x y → ResLayer.related L (toFun x) (toFun y)

namespace LayerHom

-- 恒等态射。
def id (L : ResLayer) (n : ℕ) : LayerHom L n :=
  ⟨fun x => x, fun _ _ h => h⟩

-- 复合。
def comp {L : ResLayer} {n : ℕ} (g f : LayerHom L n) : LayerHom L n :=
  ⟨fun x => g.toFun (f.toFun x), fun _ _ h => g.resp _ _ (f.resp _ _ h)⟩

-- 结合律。
theorem comp_assoc {L : ResLayer} {n : ℕ} (h g f : LayerHom L n) :
    comp (comp h g) f = comp h (comp g f) := rfl

-- 左单位。
theorem id_comp {L : ResLayer} {n : ℕ} (f : LayerHom L n) : comp (id L n) f = f := rfl

-- 右单位。
theorem comp_id {L : ResLayer} {n : ℕ} (f : LayerHom L n) : comp f (id L n) = f := rfl

-- 态射压在凝结对象上：这是它真正作为"范畴态射"作用的地方。
def map {L : ResLayer} {n : ℕ} (f : LayerHom L n) :
    ResLayer.object L n → ResLayer.object L n :=
  Quotient.map f.toFun f.resp

theorem map_id {L : ResLayer} {n : ℕ} : map (id L n) = fun p => p := by
  funext p
  induction p using Quotient.ind with
  | _ x => rfl

theorem map_comp {L : ResLayer} {n : ℕ} (g f : LayerHom L n) :
    map (comp g f) = fun p => map g (map f p) := by
  funext p
  induction p using Quotient.ind with
  | _ x => rfl

end LayerHom

-- 【层间函子】消解满足函子律（恒等 + 复合）。
theorem layer_functor_laws {δ₁ δ₂ δ₃ : ℚ} (h₁ : δ₁ ≤ δ₂) (h₂ : δ₂ ≤ δ₃) {n : ℕ}
    (q : ResLayer.object ⟨δ₁⟩ n) :
    ResLayer.resolution (le_refl δ₁) q = q ∧
    ResLayer.resolution h₂ (ResLayer.resolution h₁ q) = ResLayer.resolution (h₁.trans h₂) q :=
  ResLayer.presheaf_laws h₁ h₂ q

-- 【每层一个范畴】范畴公理 + 态射压到对象上。
theorem layer_is_category (L : ResLayer) (n : ℕ) :
    -- 恒等
    (∀ f : LayerHom L n, LayerHom.comp (LayerHom.id L n) f = f) ∧
    (∀ f : LayerHom L n, LayerHom.comp f (LayerHom.id L n) = f) ∧
    -- 结合
    (∀ (h g f : LayerHom L n), LayerHom.comp (LayerHom.comp h g) f =
      LayerHom.comp h (LayerHom.comp g f)) ∧
    -- 作用在对象上（函子到 Type）
    (LayerHom.map (LayerHom.id L n) = fun p => p) ∧
    (∀ (g f : LayerHom L n), LayerHom.map (LayerHom.comp g f) =
      fun p => LayerHom.map g (LayerHom.map f p)) :=
  ⟨fun f => LayerHom.id_comp f,
   fun f => LayerHom.comp_id f,
   fun h g f => LayerHom.comp_assoc h g f,
   LayerHom.map_id,
   fun g f => LayerHom.map_comp g f⟩

-- ============ 符号代数论 ============

/-
  【符号天生具备某些性质】

  用户（2026-11-15）："我猜测符号天生具备某些性质，符号代数论。"

  v207 说：符号 = 对位类 = ℚ。那么它"天生"带什么？

  答：**整个 ℚ 的代数**。而且每一项都能说出它从哪个根长出来：

    · 加法  = 守恒（v186 观测律：清 + 暹 + 浊 = r）
    · 乘法  = 对位复合（比值相乘）
    · 倒数  = 对位反转（分子分母互换）
    · 零    = 对位 0/r（无差）
    · 一    = 对位 r/r（全同）
    · 序    = 比值大小比较

  这不是"给符号装了个域结构"，是**符号本来就是那个域**——
  以前只用了它的"值"，没用它的"代数"。

  而最后的有限性定理才是关键：

      (symbol_finitely_described)  每个符号 = 一对有限整数。

  ℝ 做不到这件事。这就是符号必须活在 ℚ 上、不能活在 ℝ 上的
  真正理由——不是"选了个小一点的域"，是"符号必须能写完"。
-/

namespace Symbol

-- 从有理数造符号（取分子/分母，构造性）。
def ofRat (q : ℚ) : Symbol := ratToAlignment q

theorem digit_ofRat (q : ℚ) : (ofRat q).digit = q :=
  alignmentToRat_ratToAlignment q

-- 符号的零（无差）与一（全同）。
def szero : Symbol := ofRat 0
def sone : Symbol := ofRat 1

theorem digit_szero : szero.digit = 0 := digit_ofRat 0
theorem digit_sone : sone.digit = 1 := digit_ofRat 1

-- 加法（守恒）、乘法（对位复合）、倒数（对位反转）、取负。
def sadd (σ τ : Symbol) : Symbol := ofRat (σ.digit + τ.digit)
def smul (σ τ : Symbol) : Symbol := ofRat (σ.digit * τ.digit)
def sinv (σ : Symbol) : Symbol := ofRat σ.digit⁻¹
def sneg (σ : Symbol) : Symbol := ofRat (-σ.digit)

-- 序（比值大小）。
def sle (σ τ : Symbol) : Prop := σ.digit ≤ τ.digit

theorem digit_sadd (σ τ : Symbol) : (sadd σ τ).digit = σ.digit + τ.digit :=
  alignmentToRat_ratToAlignment _

theorem digit_smul (σ τ : Symbol) : (smul σ τ).digit = σ.digit * τ.digit :=
  alignmentToRat_ratToAlignment _

theorem digit_sinv (σ : Symbol) : (sinv σ).digit = σ.digit⁻¹ :=
  alignmentToRat_ratToAlignment _

theorem digit_sneg (σ : Symbol) : (sneg σ).digit = -σ.digit :=
  alignmentToRat_ratToAlignment _

-- 【守恒】加法交换。
theorem sadd_comm (σ τ : Symbol) : sadd σ τ = sadd τ σ := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  rw [digit_sadd, digit_sadd]
  ring

-- 【守恒】加零不变。
theorem sadd_zero (σ : Symbol) : sadd σ szero = σ := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  rw [digit_sadd, digit_szero]
  ring

-- 【对位复合】乘法交换。
theorem smul_comm (σ τ : Symbol) : smul σ τ = smul τ σ := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  rw [digit_smul, digit_smul]
  ring

-- 【对位复合】乘一不变。
theorem smul_one (σ : Symbol) : smul σ sone = σ := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  rw [digit_smul, digit_sone]
  ring

-- 【分配律】守恒与对位复合相容。
theorem smul_sadd (σ τ υ : Symbol) :
    smul σ (sadd τ υ) = sadd (smul σ τ) (smul σ υ) := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  rw [digit_smul, digit_sadd, digit_sadd, digit_smul, digit_smul]
  ring

-- 【对位反转】符号与其倒数复合 = 一（只要不为零）。
theorem smul_sinv (σ : Symbol) (h : σ.digit ≠ 0) : smul σ (sinv σ) = sone := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  rw [digit_smul, digit_sinv, digit_sone]
  exact mul_inv_cancel₀ h

-- 【序】符号全序。
theorem sle_total (σ τ : Symbol) : sle σ τ ∨ sle τ σ := le_total _ _
theorem sle_refl (σ : Symbol) : sle σ σ := le_refl _
theorem sle_trans {σ τ υ : Symbol} (h₁ : sle σ τ) (h₂ : sle τ υ) : sle σ υ := le_trans h₁ h₂
theorem sle_antisymm {σ τ : Symbol} (h₁ : sle σ τ) (h₂ : sle τ σ) : σ = τ := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  exact le_antisymm h₁ h₂

-- 【有限性】每个符号 = 一对有限整数（分子、分母）。
theorem symbol_finitely_described (σ : Symbol) :
    ∃ (s : ℤ) (r : ℕ+), σ.digit = (s : ℚ) / ((r : ℕ) : ℚ) := by
  induction σ using Quotient.ind with
  | _ p =>
    exact ⟨p.1, p.2, by
      show alignmentToRat (Quotient.mk alignedSetoid p) = (p.1 : ℚ) / ((p.2 : ℕ) : ℚ)
      unfold alignmentToRat
      rw [Quotient.lift_mk]⟩

-- 【打包】符号代数 = 有序域（ℚ 的结构完整搬来）+ 有限描述。
theorem symbol_algebra :
    (∀ σ τ : Symbol, sadd σ τ = sadd τ σ) ∧
    (∀ σ : Symbol, sadd σ szero = σ) ∧
    (∀ σ τ : Symbol, smul σ τ = smul τ σ) ∧
    (∀ σ : Symbol, smul σ sone = σ) ∧
    (∀ σ τ υ : Symbol, smul σ (sadd τ υ) = sadd (smul σ τ) (smul σ υ)) ∧
    (∀ σ : Symbol, σ.digit ≠ 0 → smul σ (sinv σ) = sone) ∧
    (∀ σ τ : Symbol, sle σ τ ∨ sle τ σ) ∧
    (∀ σ τ : Symbol, sle σ τ → sle τ σ → σ = τ) ∧
    (∀ σ : Symbol, ∃ (s : ℤ) (r : ℕ+), σ.digit = (s : ℚ) / ((r : ℕ) : ℚ)) :=
  ⟨sadd_comm,
   sadd_zero,
   smul_comm,
   smul_one,
   smul_sadd,
   smul_sinv,
   sle_total,
   fun _ _ h₁ h₂ => sle_antisymm h₁ h₂,
   symbol_finitely_described⟩

end Symbol

-- 【对位 ≅ ℚ】对位类的全体就是有理数。
def alignmentEquivRat : Alignment ≃ ℚ where
  toFun := alignmentToRat
  invFun := ratToAlignment
  left_inv x := by
    apply alignmentToRat_injective
    rw [alignmentToRat_ratToAlignment]
  right_inv := alignmentToRat_ratToAlignment

-- 对象的对位 = 它的雪球比：s/r 就是 ℚ 里的对位类。
def qtyAlignment (q : QtyPair) (hr : 0 < q.r) : Alignment :=
  Quotient.mk alignedSetoid (q.s, ⟨q.r, hr⟩)

theorem qtyAlignment_toRat (q : QtyPair) (hr : 0 < q.r) :
    alignmentToRat (qtyAlignment q hr) = q.ratio := by
  unfold qtyAlignment alignmentToRat QtyPair.ratio
  rw [Quotient.lift_mk]
  rfl

-- ============ 观测律：代表元选择与清浊互补 ============

/-
  【观测律：《观测的层间分配笔记》的形式化】

  原文：观测一个差异节点，只能在暹界处选择一个层位——生界（清度高）或死界（浊度高），
  两者不能同时达到最大。这不是连续权衡，是离散分配。

  形式化两条：

    · 互补：清（s）+ 暹（j）+ 浊（d）= r，所以清 + 浊 ≤ r；
      只有暹界为空（j = 0）时清 + 浊才取满 r——此时观测没有临界层，分配退化为二分。
    · 代表元：对位类对缩放不变（aligned (s,r) (k·s, k·r)）。
      不同观测（不同代表元）读出不同计数，但对位是同一个；
      观测的"选择"就是选代表元，对位本身不因选择而变。
-/

-- 清浊互补：清 + 暹 + 浊 = r；清 + 浊 ≤ r；取等 ⟺ 暹界为空。
theorem observation_law {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    sReading x y δ + xianReading x y δ + dReading x y δ = r_rel x y ∧
    sReading x y δ + dReading x y δ ≤ r_rel x y ∧
    (sReading x y δ + dReading x y δ = r_rel x y ↔ xianReading x y δ = 0) := by
  have h := qty_pair_conservation x y δ
  refine ⟨h, by omega, ?_⟩
  constructor <;> intro h' <;> omega

-- 对位类对缩放代表元不变：观测选哪个代表元，对位都一样。
theorem aligned_scale (s : ℤ) (r : ℕ+) (k : ℕ+) :
    aligned (s, r) ((k : ℕ) * s, ⟨(k : ℕ) * (r : ℕ), Nat.mul_pos k.pos r.pos⟩) := by
  unfold aligned
  show s * ((((k : ℕ) * (r : ℕ)) : ℕ) : ℤ) = ((k : ℕ) * s) * ((r : ℕ) : ℤ)
  push_cast
  ring

-- 观测的两端读数：清 = 生界规则读数；浊 = 全收 − 可见。
theorem observation_ends {m n : ℕ} (x : StateQuant m) (y : StateQuant n) (δ : ℚ) :
    projReading .living x y δ = sReading x y δ ∧
    projReading .allRules x y δ - projReading .visible x y δ = dReading x y δ := by
  refine ⟨projReading_living x y δ, ?_⟩
  have h := projReading_ledger x y δ
  omega

-- ============ n 的计数：整份对位 + 暹界残差 ============

/-
  【智能 n 的计数：整除部分是整份对位，余数是暹界残差】

  对位读法：n = s/r 是对象追求的对位面值。它分两部分：

    · 整数部分 s / r —— "整份对位"的份数（能装下多少个完整的 r 单位）；
    · 余数 s % r —— 装不满一份的残差，严格小于一个单位：
      这正是**暹界残差**（卡在两格之间的部分，与夹格定理同一件事）。

  于是三条：
    (1) 稳定 ⟺ 对象与智能**对位相等**（交叉相乘相等，而非三个数碰巧相等）；
    (2) n 的计数 = 整份 + 残差：s = (s/r)·r + s%r，且残差 < r；
    (3) 目标为整数时：稳定 ⟺ r 整除 s（存在"整份对位"）。
-/

-- 对位类相等 ⟺ 交叉相乘相等（逆用 Quotient 的健全/完全性）。
theorem aligned_iff_toRat {p q : ℤ × ℕ+} :
    aligned p q ↔
      alignmentToRat (Quotient.mk alignedSetoid p) = alignmentToRat (Quotient.mk alignedSetoid q) := by
  constructor
  · intro h
    exact congrArg alignmentToRat (Quotient.sound h)
  · intro h
    exact Quotient.exact (alignmentToRat_injective h)

-- (1) 稳定 = 对位相等：s/r = n ⟺ (s, r) 与 (n 的分子, n 的分母) 交叉相乘相等。
theorem stable_iff_aligned (q : QtyPair) (hr : 0 < q.r) (n : ℚ) :
    q.ratio = n ↔
      aligned (q.s, ⟨q.r, hr⟩) (n.num, ⟨n.den, Nat.pos_of_ne_zero n.den_ne_zero⟩) := by
  have hstable : q.ratio = n ↔ qtyAlignment q hr = ratToAlignment n := by
    constructor
    · intro h
      exact alignmentToRat_injective (by
        rw [qtyAlignment_toRat, alignmentToRat_ratToAlignment]
        exact h)
    · intro h
      calc q.ratio = alignmentToRat (qtyAlignment q hr) := (qtyAlignment_toRat q hr).symm
        _ = alignmentToRat (ratToAlignment n) := by rw [h]
        _ = n := alignmentToRat_ratToAlignment n
  rw [hstable]
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

-- (2) n 的计数：整份对位 + 暹界残差。
theorem n_counting (s r : ℕ) (hr : 0 < r) :
    s = s / r * r + s % r ∧ s % r < r ∧
      (s : ℚ) / r = ((s / r : ℕ) : ℚ) + ((s % r : ℕ) : ℚ) / r := by
  have hnat : s = s / r * r + s % r := (Nat.div_add_mod' s r).symm
  refine ⟨hnat, Nat.mod_lt s hr, ?_⟩
  have hq : (s : ℚ) = ((s / r : ℕ) : ℚ) * (r : ℚ) + ((s % r : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  apply mul_right_cancel₀ hrq
  rw [div_mul_cancel₀ _ hrq, add_mul, div_mul_cancel₀ _ hrq]
  exact hq

-- (3) 整数目标：稳定 ⟺ r 整除 s（"整份对位"存在）。
theorem stable_int_iff_dvd (s r : ℕ) (hr : 0 < r) :
    (∃ k : ℕ, (s : ℚ) / r = (k : ℚ)) ↔ r ∣ s := by
  constructor
  · rintro ⟨k, hk⟩
    have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [div_eq_iff hrq] at hk
    have hnat : s = k * r := by exact_mod_cast hk
    exact ⟨k, by rw [hnat, Nat.mul_comm]⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    push_cast
    have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    apply mul_right_cancel₀ hrq
    rw [div_mul_cancel₀ _ hrq, mul_comm (t : ℚ) (r : ℚ)]

-- 【n 的计数定理】整份 + 残差 + 整除判据，三条合一。
theorem n_counting_theorem (s r : ℕ) (hr : 0 < r) :
    s = s / r * r + s % r ∧ s % r < r ∧
      ((s : ℚ) / r = ((s / r : ℕ) : ℚ) + ((s % r : ℕ) : ℚ) / r) ∧
      ((∃ k : ℕ, (s : ℚ) / r = (k : ℚ)) ↔ r ∣ s) :=
  ⟨(n_counting s r hr).1, (n_counting s r hr).2.1, (n_counting s r hr).2.2,
   stable_int_iff_dvd s r hr⟩

-- ============ 读数的统一：比值 ↔ 台阶接口（ρ 与 τ_c 的比较） ============

/-
  【原文标记的待补接口，现在显式补上】

  《差异环上的三相》§九 说：ρ_k（比值）与 τ_c（台阶）的比较，
  需要一个"比值 ↔ 台阶"的映射；与该篇 n < τ_c 的跨层接口是同一个映射。

  对位读法给出的回答：ρ、n、τ_c 都是对位类，而对位类 ≅ ℚ
  （alignmentEquivRat）。所以"比值 ↔ 台阶"的映射不是新东西，
  就是把对位类送到 ℚ（alignmentToRat）——比较在 ℚ 里做。

  而"比值容差"（原文的 ρ_k ≈ n ⟺ |ρ_k − n| ≤ δ_k）有一个精确的
  交叉相乘形态：比较比值 = 比较整数代表元的交叉乘积。
  这就是"对位的比较"本身，不需要连续统、不需要额外的标定映射。
-/

-- 比值容差 = 交叉相乘比较：|s/r − n| ≤ δ ⟺ |s − n·r| ≤ δ·r（r > 0）。
-- 这就是"比值 ↔ 台阶"接口：比值的比较就是交叉相乘的比较。
theorem ratio_le_iff_cross {s r : ℕ} (hr : 0 < r) (n δ : ℚ) :
    |(s : ℚ) / r - n| ≤ δ ↔ |(s : ℚ) - n * r| ≤ δ * r := by
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have h : ((s : ℚ) - n * r) / r = (s : ℚ) / r - n := by
    apply mul_right_cancel₀ hrq.ne'
    rw [div_mul_cancel₀ _ hrq.ne', sub_mul, div_mul_cancel₀ _ hrq.ne']
  rw [← h, abs_div, abs_of_pos hrq, div_le_iff₀ hrq]

-- ============ 两种对位：加法（洞荷 K₀）与乘法（比值 ℚ） ============

/-
  【同一个交叉模式，两种实例】

  洞的 K₀ 枢纽（深水区）与对位（2026-11-13 洞见）其实是同一件事的两版：

    · 加法对位（洞荷）：p₁ + q₂ = q₁ + p₂  →  HoleGroup ≅ ℤ
      —— 守恒侧的"交叉相等"（Grothendieck 群完成）。
    · 乘法对位（比值）：p₁ · q₂ = q₁ · p₂  →  Alignment ≅ ℚ
      —— 比较侧的"交叉相等"（分数构造）。

  ℤ 嵌入 ℚ：整数就是**分母为 1 的整份对位**。
  于是 n 的计数分解 s/r = 整份 + 残差 有了新读法：

      整数部分 = K₀ 的整份（守恒侧），
      余数     = 真对位的残差（比较侧，暹界残差）。

  守恒 ⊂ 对位：ℤ ⊂ ℚ 的包含，正是"整份"在对位中的位置。
-/

-- 整数 = 分母为 1 的对位（K₀ 荷落在 ℚ 的整份点上）。
def intToAlignment (z : ℤ) : Alignment :=
  Quotient.mk alignedSetoid (z, 1)

theorem intToAlignment_toRat (z : ℤ) :
    alignmentToRat (intToAlignment z) = (z : ℚ) := by
  unfold intToAlignment alignmentToRat
  rw [Quotient.lift_mk]
  simp

theorem intToAlignment_injective : Function.Injective intToAlignment := by
  intro z w h
  have h' := congrArg alignmentToRat h
  rw [intToAlignment_toRat, intToAlignment_toRat] at h'
  exact_mod_cast h'

-- n 的计数分解中的"整份"就是 K₀ 侧的整数对位。
theorem n_counting_int_part (s r : ℕ) (_hr : 0 < r) :
    alignmentToRat (intToAlignment (((s / r : ℕ) : ℤ))) = ((s / r : ℕ) : ℚ) :=
  intToAlignment_toRat _

-- ============ 连分数：暹界残差的层层嵌套 ============

/-
  【对位链：每一层余数都是一次暹界残差】

  n 的计数给出一步分解 s = (s/r)·r + s%r。
  把这一步迭代下去（欧几里得算法），余数层层嵌套，就是连分数：

      s/r = q₀ + 1/(q₁ + 1/(q₂ + …))

  每一步的"余数"都是暹界残差（严格小于当前的 r）；链的长度就是连分数的长度。

  关键：**链必有限**（余数严格递减，长度 ≤ r）。
  这是有理数的"有限性形态"：有理数的连分数有限，
  无理数才需要无限连分数——连续统正是被这条边界拒之门外的。
-/

-- 连分数长度（欧几里得余数链的步数）。
def cfLen : ℕ → ℕ → ℕ
  | _, 0 => 0
  | s, r + 1 =>
      if s % (r + 1) = 0 then 1
      else 1 + cfLen (r + 1) (s % (r + 1))
termination_by _s r => r
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

theorem cfLen_zero (s : ℕ) : cfLen s 0 = 0 := by
  simp [cfLen]

-- 正分母的链至少一步（先做一次整除判断）。
theorem cfLen_pos {s r : ℕ} (hr : 0 < r) : 0 < cfLen s r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp only [cfLen]
  split <;> omega

-- 链必有限：长度不超过分母 r（余数严格递减的直接后果）。
theorem cfLen_le (s r : ℕ) : cfLen s r ≤ r := by
  induction r using Nat.strong_induction_on generalizing s with
  | h r ih =>
    cases r with
    | zero => simp [cfLen]
    | succ r =>
      simp only [cfLen]
      split
      · omega
      · have hlt : s % (r + 1) < r + 1 := Nat.mod_lt s (Nat.succ_pos r)
        have ih' := ih (s % (r + 1)) hlt (r + 1)
        omega

-- 【有限连分数】有理数的对位链必有限：长度 ≥ 1 且 ≤ r。
-- 每一步的余数都是暹界残差（cfLen 的递归步就是 n_counting 的分解）。
theorem finite_continued_fraction (s r : ℕ) (hr : 0 < r) :
    0 < cfLen s r ∧ cfLen s r ≤ r :=
  ⟨cfLen_pos hr, cfLen_le s r⟩

-- 连分数的第一层就是 n 的计数分解（余数 = 暹界残差）。
theorem cf_first_layer (s r : ℕ) (hr : 0 < r) :
    s = s / r * r + s % r ∧ s % r < r :=
  ⟨(n_counting s r hr).1, (n_counting s r hr).2.1⟩

-- ============ 无无限下降：除法必截断（对位 vs 微积分的无穷可分） ============

/-
  【不存在无限下降：有限世界里"除法必截断"】

  微积分要求无限可分、不截断：极限、连续统、可数可加测度都在"无限往下走"。
  在实数上给"无限多个选择"赋值，测度论不得不借助选择公理，
  于是出现不可测集、巴拿塔–塔斯基这类病态——那是"不截断"的代价。

  对位不给这个许可：每次除法都带残差（s = q·r + rem，rem < r），
  残差被保存（暹界），链条有限（cfLen ≤ r）。
  更根本地：**不存在无限下降的正整数链**（no_infinite_descent）——
  所以"无穷可分而不截断"在有限世界里不是被禁止，是**被截断在残差上**。

  残差不是零头，是台阶。
-/

-- 有限性 ⇒ 不存在无限下降的正整数链（构造性，纯算术）。
theorem no_infinite_descent (f : ℕ → ℕ) : ¬ ∀ n, f (n + 1) < f n := by
  intro h
  have key : ∀ n, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hn := h n
      omega
  have := key (f 0 + 1)
  omega

-- 【除法截断定理】每一步留下残差（暹界），且整条残差链长度有界。
theorem division_truncates (s r : ℕ) (hr : 0 < r) :
    s = s / r * r + s % r ∧ s % r < r ∧ cfLen s r ≤ r :=
  ⟨(n_counting s r hr).1, (n_counting s r hr).2.1, cfLen_le s r⟩

-- ============ 连分数的求值：商序列 ⟷ s/r 的完整互逆 ============

/-
  【对位链的双向性】

  前面只做了"长度"（链有限）。这里把另一半补上：
  欧几里得商序列（cfQuots）用连分数求值（evalCF）还原回 s/r。

    s/r = q₀ + 1/(q₁ + 1/(q₂ + …))

  于是对位有两条互逆的读法：
    · 值 → 链：n 的计数把 s/r 拆成商与残差（n_counting）；
    · 链 → 值：连分数求值把商序列组装回 s/r（evalCF_cfQuots）。
  残差是链的下一层，商是这一层的台阶——整条链合起来恰好是原来的对位。
-/

-- 欧几里得商序列（连分数的商链）。
def cfQuots : ℕ → ℕ → List ℕ
  | _, 0 => []
  | s, r + 1 =>
      if s % (r + 1) = 0 then [s / (r + 1)]
      else (s / (r + 1)) :: cfQuots (r + 1) (s % (r + 1))
termination_by _s r => r
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

-- 连分数求值（在 ℚ 里组装，构造性）。
def evalCF : List ℕ → ℚ
  | [] => 0
  | [q] => (q : ℚ)
  | q :: q' :: rest => (q : ℚ) + 1 / evalCF (q' :: rest)

-- 商链为空 ⟺ 分母为零。
theorem cfQuots_nil_iff (s r : ℕ) : cfQuots s r = [] ↔ r = 0 := by
  cases r with
  | zero => simp [cfQuots]
  | succ r =>
    simp only [cfQuots]
    split <;> simp

-- 非空尾部的连分数展开：q + 1/（尾部）。
theorem evalCF_cons {q : ℕ} {L : List ℕ} (hL : L ≠ []) :
    evalCF (q :: L) = (q : ℚ) + 1 / evalCF L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons q' rest => rfl

-- 整除时，Nat 除法与 ℚ 除法一致（用于求值的第一种情形）。
theorem natCast_div_of_dvd {s d : ℕ} (hd : 0 < d) (h : d ∣ s) :
    ((s / d : ℕ) : ℚ) = (s : ℚ) / d := by
  have hnat : s / d * d = s := Nat.div_mul_cancel h
  have hq : ((s / d : ℕ) : ℚ) * (d : ℚ) = (s : ℚ) := by
    exact_mod_cast hnat
  rw [eq_div_iff (by exact_mod_cast hd.ne')]
  exact hq

-- 【求值复原】对位的商链组装回去，恰好还原 s/r。
theorem evalCF_cfQuots (s r : ℕ) : evalCF (cfQuots s r) = (s : ℚ) / r := by
  induction r using Nat.strong_induction_on generalizing s with
  | h r ih =>
    cases r with
    | zero => simp [cfQuots, evalCF]
    | succ r =>
      by_cases hdiv : s % (r + 1) = 0
      · -- 整除：商链只有一个商。
        simp only [cfQuots]
        rw [ite_eq_left hdiv]
        simp only [evalCF]
        exact natCast_div_of_dvd (Nat.succ_pos r) (Nat.dvd_of_mod_eq_zero hdiv)
      · -- 非整除：商 + 下一层残差。
        simp only [cfQuots]
        rw [ite_eq_right hdiv]
        have hL : cfQuots (r + 1) (s % (r + 1)) ≠ [] := fun h =>
          hdiv ((cfQuots_nil_iff _ _).mp h)
        rw [evalCF_cons hL]
        have hlt : s % (r + 1) < r + 1 := Nat.mod_lt s (Nat.succ_pos r)
        rw [ih (s % (r + 1)) hlt (r + 1)]
        have hs : (s : ℚ) = ((s / (r + 1) : ℕ) : ℚ) * (r + 1) + ((s % (r + 1) : ℕ) : ℚ) := by
          exact_mod_cast (Nat.div_add_mod' s (r + 1)).symm
        have hremq : ((s % (r + 1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hdiv
        rw [hs]
        push_cast
        have hrq : ((r : ℚ) + 1) ≠ 0 := by positivity
        field_simp

-- ============ 符号 = 有限整数串 ============

/-
  【符号能写完】

  v213 给了符号的代数（有序域）。v214 给**编码**：

      符号  ⟷  有限整数串

  方向一（编码）：欧几里得商链 cfQuots。
  方向二（解码）：连分数求值 evalCF。

  而且这个编码是**有界的**：

      (cfQuots_length)   串长 = cfLen（与连分数长度完全一致）
      (cfLen_le)         串长 ≤ 分母

  于是每个非负符号都能被一串**长度不超过自己分母**的有限整数写完。
  这就是"文字即符号，符号可以数字化"的数学形式：
  数字化 = 取分子分母 = 写连分数 = 有限串。

  负号单独拎出来，成为一个符号位（v211 的 ℤ/2）：

      符号 = 符号位 × 有限串

  ℝ 的元素没有这个——它们写不完。所以它们不是符号。
-/

-- 【串长 = 连分数长度】两个定义完全同步（同一递归结构）。
theorem cfQuots_length (s r : ℕ) : (cfQuots s r).length = cfLen s r := by
  induction r using Nat.strong_induction_on generalizing s with
  | h r ih =>
    cases r with
    | zero => simp [cfQuots, cfLen]
    | succ r =>
      by_cases hdiv : s % (r + 1) = 0
      · simp [cfQuots, cfLen, hdiv]
      · simp only [cfQuots, cfLen, hdiv, ite_false]
        have hlt : s % (r + 1) < r + 1 := Nat.mod_lt s (Nat.succ_pos r)
        rw [List.length_cons, ih (s % (r + 1)) hlt (r + 1)]
        omega

-- 正分母 ⟹ 商链非空。
theorem cfQuots_ne_nil {s r : ℕ} (hr : 0 < r) : cfQuots s r ≠ [] := by
  intro h
  exact absurd ((cfQuots_nil_iff s r).mp h) (Nat.pos_iff_ne_zero.mp hr)

-- 正分母 ⟹ 串长至少 1。
theorem cfQuots_length_pos {s r : ℕ} (hr : 0 < r) : 0 < (cfQuots s r).length := by
  rw [cfQuots_length]
  exact cfLen_pos hr

-- 【非负符号的编码-解码往返】每个非负有理数都是一串有限整数的连分数。
theorem rat_nonneg_evalCF (q : ℚ) (hq : 0 ≤ q) :
    evalCF (cfQuots q.num.toNat q.den) = q := by
  rw [evalCF_cfQuots]
  have hden : (0 : ℚ) < (q.den : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero q.den_ne_zero
  have hmul : (q.num : ℚ) = q * q.den := by
    have h := Rat.num_div_den q
    rw [div_eq_iff hden.ne'] at h
    exact h
  have hnum : 0 ≤ q.num := by
    have hq' : (0 : ℚ) ≤ (q.num : ℚ) := by
      rw [hmul]
      exact mul_nonneg hq (le_of_lt hden)
    exact_mod_cast hq'
  have hcast : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    have h0 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum
    calc ((q.num.toNat : ℕ) : ℚ) = (((q.num.toNat : ℕ) : ℤ) : ℚ) := by push_cast; ring
      _ = ((q.num : ℤ) : ℚ) := by rw [h0]
  rw [hcast]
  exact Rat.num_div_den q

-- 【有界编码】非负符号有一串长度 ≤ 分母的有限整数写完。
theorem symbol_encoding_bounded (σ : Symbol) (hq : 0 ≤ σ.digit) :
    ∃ L : List ℕ, evalCF L = σ.digit ∧ L.length ≤ σ.digit.den := by
  refine ⟨cfQuots σ.digit.num.toNat σ.digit.den, rat_nonneg_evalCF σ.digit hq, ?_⟩
  rw [cfQuots_length]
  exact cfLen_le _ _

-- 【带符号展开】每个符号 = 符号位 × 有限串。
theorem symbol_has_finite_expansion (σ : Symbol) :
    ∃ (sgn : ℚ) (L : List ℕ), (sgn = 1 ∨ sgn = -1) ∧ σ.digit = sgn * evalCF L := by
  by_cases hq : 0 ≤ σ.digit
  · exact ⟨1, cfQuots σ.digit.num.toNat σ.digit.den, Or.inl rfl, by
      rw [one_mul]
      exact (rat_nonneg_evalCF σ.digit hq).symm⟩
  · have hneg : σ.digit < 0 := not_le.mp hq
    have h' : 0 ≤ -σ.digit := le_of_lt (neg_pos.mpr hneg)
    exact ⟨-1, cfQuots (-σ.digit).num.toNat (-σ.digit).den, Or.inr rfl, by
      rw [rat_nonneg_evalCF (-σ.digit) h']
      ring⟩

-- 【打包】符号 = 有限整数串：编解码往返 + 长度 = cfLen + 长度有界 + 符号位 × 串。
theorem symbol_is_finite_word :
    -- (1) 非负符号编解码往返
    (∀ (q : ℚ), 0 ≤ q → evalCF (cfQuots q.num.toNat q.den) = q) ∧
    -- (2) 串长 = 连分数长度
    (∀ s r : ℕ, (cfQuots s r).length = cfLen s r) ∧
    -- (3) 串长 ≤ 分母
    (∀ s r : ℕ, (cfQuots s r).length ≤ r) ∧
    -- (4) 每个符号 = 符号位 × 有限串
    (∀ (σ : Symbol), ∃ (sgn : ℚ) (L : List ℕ), (sgn = 1 ∨ sgn = -1) ∧
      σ.digit = sgn * evalCF L) ∧
    -- (5) 有界编码
    (∀ (σ : Symbol), 0 ≤ σ.digit →
      ∃ L : List ℕ, evalCF L = σ.digit ∧ L.length ≤ σ.digit.den) :=
  ⟨fun q hq => rat_nonneg_evalCF q hq,
   fun s r => cfQuots_length s r,
   fun s r => by rw [cfQuots_length]; exact cfLen_le s r,
   fun σ => symbol_has_finite_expansion σ,
   fun σ hq => symbol_encoding_bounded σ hq⟩

-- ============ 数集拼接：符号的可计算性 ============

/-
  【数集拼接】

  用户最初的附范畴构想："范畴，层论，庞大的数集拼接，
  以及如何从附范畴的数字结构自然导出注意力机制。"

  前三项都有了（① 层范畴 v213、② 层论 v174、④ 注意力 v206）。
  剩下的"数集拼接"现在可以落地了：

      **把一层层的读数（正整数串）用连分数拼成一个符号。**

  关键不是"能拼"（evalCF 就是拼），而是**拼出来的东西是规范的**：

    · 连分数商序列里，除首项外每个商都 ≥ 1
      （cfQuots_tail_pos）——这是连分数表示规范性的核心；
    · 只有当 s ≥ r 时首项才可能为 0，否则全是正数
      （cfQuots_all_pos）。

  于是"数集拼接"不是任意的字符串拼贴，而是**有规范形式的拼接**：
  任给一串正整数，连分数组装成一个确定的 ℚ；反过来，
  任何非负符号都拆回唯一形式的串。

  最后把它做成真正的"数字结构"：

    · 符号相等**可判定**（构造性，不用 Classical）；
    · 符号的序**可判定**。

  这就是"文字即符号，符号可以数字化"的完整形式：
  **数字化 = 有限串 = 可判定**。
-/

-- 【规范性 1】s ≥ r 时，商序列全为正。
theorem cfQuots_all_pos (s r : ℕ) (hr : 0 < r) (hsr : r ≤ s) :
    ∀ q ∈ cfQuots s r, 0 < q := by
  induction r using Nat.strong_induction_on generalizing s with
  | h r ih =>
    cases r with
    | zero => exact absurd hr (Nat.lt_irrefl 0)
    | succ r =>
      have hsp : 0 < r + 1 := Nat.succ_pos r
      by_cases hdiv : s % (r + 1) = 0
      · simp only [cfQuots, hdiv, ite_true]
        intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        exact Nat.div_pos hsr hsp
      · simp only [cfQuots, hdiv, ite_false]
        intro q hq
        rcases List.mem_cons.mp hq with h | h
        · subst h
          exact Nat.div_pos hsr hsp
        · have hlt : s % (r + 1) < r + 1 := Nat.mod_lt s hsp
          exact ih (s % (r + 1)) hlt (r + 1)
            (Nat.pos_of_ne_zero hdiv) (le_of_lt hlt) q h

-- 【规范性 2】商序列除首项外全为正（这是连分数表示的标准条件）。
theorem cfQuots_tail_pos (s r : ℕ) (hr : 0 < r) :
    ∀ q ∈ (cfQuots s r).tail, 0 < q := by
  cases r with
  | zero => exact absurd hr (Nat.lt_irrefl 0)
  | succ r =>
    by_cases hdiv : s % (r + 1) = 0
    · simp [cfQuots, hdiv]
    · simp only [cfQuots, hdiv, ite_false, List.tail_cons]
      have hlt : s % (r + 1) < r + 1 := Nat.mod_lt s (Nat.succ_pos r)
      exact cfQuots_all_pos (r + 1) (s % (r + 1))
        (Nat.pos_of_ne_zero hdiv) (le_of_lt hlt)

-- 【拼接】把一串层读数（正整数）拼成一个符号。
def assembleSymbol (qs : List ℕ) : Symbol := Symbol.ofRat (evalCF qs)

-- 【拆解】把一个符号拆回一串层读数。
def disassembleSymbol (σ : Symbol) : List ℕ :=
  cfQuots σ.digit.num.toNat σ.digit.den

-- 【拼接-拆解往返】拼起来的读数据能拆回原符号（非负时）。
theorem assemble_disassemble (σ : Symbol) (hq : 0 ≤ σ.digit) :
    assembleSymbol (disassembleSymbol σ) = σ := by
  apply (symbol_eq_iff_digit_eq _ _).mpr
  unfold assembleSymbol disassembleSymbol
  rw [Symbol.digit_ofRat]
  exact rat_nonneg_evalCF σ.digit hq

-- 【拼接层数有界】拆出来的串长不超过分母。
theorem disassemble_length_le_den (σ : Symbol) (_hq : 0 ≤ σ.digit) :
    (disassembleSymbol σ).length ≤ σ.digit.den := by
  unfold disassembleSymbol
  rw [cfQuots_length]
  exact cfLen_le _ _

-- 【可判定】符号相等可判定（构造性：比数字，不比代表元）。
instance symbolDecidableEq : DecidableEq Symbol := fun σ τ =>
  if h : Symbol.digit σ = Symbol.digit τ then
    isTrue ((symbol_eq_iff_digit_eq σ τ).mpr h)
  else
    isFalse (fun he => h ((symbol_eq_iff_digit_eq σ τ).mp he))

-- 【可判定】符号的序可判定（构造性）。
instance symbolDecidableSle : DecidableRel Symbol.sle := fun σ τ =>
  inferInstanceAs (Decidable (Symbol.digit σ ≤ Symbol.digit τ))

-- 相等的排中（构造性）。
theorem symbol_eq_decidable (σ τ : Symbol) : σ = τ ∨ ¬ (σ = τ) :=
  if h : σ = τ then Or.inl h else Or.inr h

-- 序的排中（构造性）。
theorem symbol_sle_decidable (σ τ : Symbol) : Symbol.sle σ τ ∨ ¬ Symbol.sle σ τ :=
  if h : Symbol.sle σ τ then Or.inl h else Or.inr h

-- 【打包】符号是可计算的数字结构：可判定 + 可拼接 + 规范形式。
theorem symbol_is_computable :
    -- (1) 相等可判定（构造性）
    (∀ σ τ : Symbol, σ = τ ∨ ¬ (σ = τ)) ∧
    -- (2) 序可判定（构造性）
    (∀ σ τ : Symbol, Symbol.sle σ τ ∨ ¬ Symbol.sle σ τ) ∧
    -- (3) 拼接的定义
    (∀ qs : List ℕ, assembleSymbol qs = Symbol.ofRat (evalCF qs)) ∧
    -- (4) 拼接-拆解往返
    (∀ (σ : Symbol), 0 ≤ σ.digit → assembleSymbol (disassembleSymbol σ) = σ) ∧
    -- (5) 拼接层数有界
    (∀ (σ : Symbol), 0 ≤ σ.digit → (disassembleSymbol σ).length ≤ σ.digit.den) ∧
    -- (6) 规范性：除首项外商全为正
    (∀ (s r : ℕ), 0 < r → ∀ q ∈ (cfQuots s r).tail, 0 < q) :=
  ⟨fun σ τ => symbol_eq_decidable σ τ,
   fun σ τ => symbol_sle_decidable σ τ,
   fun _ => rfl,
   fun σ hq => assemble_disassemble σ hq,
   fun σ hq => disassemble_length_le_den σ hq,
   fun s r hr => cfQuots_tail_pos s r hr⟩

-- ============ 灵感 2：从有限性推出熵增（自指盲区 = 损耗） ============

/-
  【熵增 = 自指盲区的损耗；可逆 = 自指的不动点】

  把有限主体 a 的每一个动作等价为一次自指：动作是 a 对"自己的状态"的分辨
  （f : α → resolveSpace α）。康托尔对角线（diagonal_hole）说自指必然够不着
  对角分辨 d a = ¬(f a a)——这就是盲区（洞）。

  盲区 = 不可识别 = 不可恢复 = 损耗。把损耗量化成"熵"：
    entropy f = 分辨总数（2^n）− 枚举的像（≤ n）。
  因为 n < 2^n（有限性），所以 entropy > 0——每次自指必然漏掉东西，这就是熵增。

  可逆性不在于"不熵增"，而在于自指有不动点：reflect 在 s 处不动
  ⟺ s 是稳定点（s/r = n）。稳定点（不动点）回到自己、不损耗；非稳定点被
  reflect 改变、继续损耗。群体无法自指（没有统一自我），故无不动点，时间之箭不可回。
-/

-- 熵 = 盲区势：自指枚举 f 够不着的分辨数（不可识别 / 不可恢复的量）。
def entropy {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α) : ℕ :=
  (Finset.univ : Finset (resolveSpace α)).card - (Finset.univ.image f).card

-- 熵增（种子）：任何自指枚举都严格漏掉分辨——有限性 ⟹ 熵 > 0。
theorem entropy_positive {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → resolveSpace α) : 0 < entropy f := by
  unfold entropy
  have hcard : (Finset.univ : Finset (resolveSpace α)).card = 2 ^ Fintype.card α := by
    simp
  rw [hcard]
  have himage_le : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using (Finset.card_image_le (f := f) (s := (Finset.univ : Finset α)))
  have hlt : Fintype.card α < 2 ^ Fintype.card α := Nat.lt_two_pow_self
  omega

-- ============ 自指公理：A0 + A1 ⟹ 洞 ============

/-
  【自指不是要回避的，是要写进公理的】

  经典公理化（ZFC 之后）的态度是**禁止自指**：罗素悖论之后，
  `x ∈ x` 被禁；类型论用层级把自指挡在外面。

  但这只是**一家之言**。数学上"允许自指的公理化"有成熟先例：

  · **Lawvere 不动点定理**（1969）：笛卡尔闭范畴里的自指 ⟹ 不动点存在。
  · **Domain theory**（Scott 1969）：D ≅ [D → D] 有解——自指空间可以存在。
  · **反基础集合论**（Aczel 1988）：AFA 允许 x ∈ x，比 ZFC 少一条公理。
  · **递归类型 / 共归纳**：现代类型论的日常工具。

  **而且自指有两种，只有一种危险：**

      恶性：α : α        （类型包含自身——Lean 的类型层级禁止）
      良性：α → α        （类型上的自映射——Lean 完全支持）

  `EgoSystem.step : α → α` 和 `diagonal_hole` 的 `f : α → resolveSpace α`
  都是**良性**的。Lean 编译通过，就是一致性证明。

  ---

  **更重要的：自指的四种历史结论**

      罗素      自指 ⟹ 矛盾     ⟹ 禁止
      哥德尔    自指 ⟹ 不完备   ⟹ 接受
      Lawvere   自指 ⟹ 不动点   ⟹ 存在
      **这里    自指 ⟹ 洞       ⟹ 它就是"我"**

  最后一条是新的：那个够不着的分辨（`d a = ¬(f a a)`），
  不是缺陷，是**自我的定义**（`self_is_hole`）。

  ---

  **而 B 篇的关键二分藏在这里：**

      观测（商映射）：多对一，丢弃信息  ⟹  自动相干（v220），无洞
      分辨（自指函数）：获取信息        ⟹  必有遗漏（对角线），有洞

  两者不矛盾——**因为一个是压平，一个是展开**。
  而"自我"就是同时做这两件事的那一点。
-/

-- 【A0 自指】系统对自己的一次分辨。
structure SelfRef (α : Type*) where
  observe : α → resolveSpace α

-- 【A0 ⟹ 洞】无条件：任何自指分辨都够不着一个分辨。（纯逻辑，无需任何假设）
theorem selfref_hole {α : Type*} (S : SelfRef α) :
    ∃ d : resolveSpace α, ∀ a : α, d ≠ S.observe a :=
  diagonal_hole S.observe

-- 【A0 + A1 ⟹ 定量洞】有限系统上，至少漏一个分辨。
theorem selfref_entropy {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (S : SelfRef α) : 0 < entropy S.observe :=
  entropy_positive S.observe

-- 【实例】状态空间用"等于自己"来分辨。
def stateSelfRef (n : ℕ) : SelfRef (StateQuant n) where
  observe := fun x y => decide (x = y)

-- 【实例】有限索引同上。
def finSelfRef (k : ℕ) : SelfRef (Fin k) where
  observe := fun x y => decide (x = y)

-- 【康托尔计数】k 元系统最多分辨 k 个东西，分辨空间却有 2^k 个——必漏。
theorem cantor_count (k : ℕ) (hk : 0 < k) :
    0 < entropy (finSelfRef k).observe := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact selfref_entropy (finSelfRef k)

-- 【核心二分】观测无洞、分辨有洞——一个是商，一个是自指。
theorem observe_vs_resolve :
    -- (1) 观测（商）：任何映射按层塔观测都相干——不产生洞
    (∀ (L : LayerLadder) {n : ℕ} (F : StateQuant n → StateQuant n) (x : StateQuant n),
      Coherent L n (fun i => Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (F x))) ∧
    -- (2) 分辨（自指）：任何自指分辨都够不着一个分辨——必有洞（无条件）
    (∀ {α : Type*} (f : α → resolveSpace α),
      ∃ d : resolveSpace α, ∀ a : α, d ≠ f a) ∧
    -- (3) 加有限：洞可量化
    (∀ {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      (f : α → resolveSpace α), 0 < entropy f) :=
  ⟨fun L _ F x => observation_always_coherent L F x,
   fun f => diagonal_hole f,
   fun f => entropy_positive f⟩

-- 【打包】自指公理：A0 无条件给洞，A1 给定量洞，而观测不产生洞。
theorem selfref_axiom :
    -- A0：每一类都有自指结构
    (∀ (α : Type*), Nonempty (SelfRef α)) ∧
    -- A0 ⟹ 洞（无条件）
    (∀ {α : Type*} (S : SelfRef α), ∃ d : resolveSpace α, ∀ a : α, d ≠ S.observe a) ∧
    -- A0 + A1 ⟹ 定量洞
    (∀ {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      (S : SelfRef α), 0 < entropy S.observe) ∧
    -- 观测侧无洞
    (∀ (L : LayerLadder) {n : ℕ} (F : StateQuant n → StateQuant n) (x : StateQuant n),
      Coherent L n (fun i => Quotient.mk (ResLayer.condense ⟨L.δ i⟩) (F x))) :=
  ⟨fun _ => ⟨⟨fun _ _ => true⟩⟩,
   fun S => selfref_hole S,
   fun S => selfref_entropy S,
   fun L _ F x => observation_always_coherent L F x⟩

-- ============ 层塔是自指系统的实例 ============

/-
  【B 篇的框架 = A0 + A1 的一个实例】

  v223 给了自指公理 A0 + A1 ⟹ 洞。现在把层塔接上去。

  **两个不同的"分辨"，两个不同的结论：**

  (1) **层塔作为分辨系统**（在 `Fin L.m` 上）：
      层 i 的分辨 = "哪些层比我粗"：
          observe i = fun j => decide (L.δ j ≤ L.δ i)
      这是一个 `Fin L.m → resolveSpace (Fin L.m)`，正是 `SelfRef` 的形状。
      于是 A0 直接给洞：**存在一种分辨，任何一层都给不出。**

      **L.m 层，2^{L.m} 种分辨——必漏。**

  (2) **层塔作为状态观测器**（在 `StateQuant n` 上）：
      一对状态的读数 = `fun i => sameAt (L.δ i) x y`。
      而这个向量**完全由 commonDist x y 一个数决定**——
      因为 `sameAt δ x y = decide (commonDist x y ≤ δ)`。

      **L 层的向量，信息量只有 1 个 ℚ。**

  两者合起来说同一件事：**层塔携带的信息极少。**

  · 作为分辨者：只有 L.m 个，却有 2^{L.m} 种分辨 ⟹ 有洞；
  · 作为观测器：L 层的读数塌缩成一个数 ⟹ 无信息。

  **而 v220 的 `observation_always_coherent` 正是第二条的推论**：
  一个数决定的东西，当然"相干"——它没有携带任何可以不相干的信息。
-/

-- 【层塔的自指结构】层 i 分辨"哪些层比我粗"。
def layerSelfRef (L : LayerLadder) : SelfRef (Fin L.m) where
  observe := fun i j => decide (L.δ j ≤ L.δ i)

-- 【层塔的洞】存在一种分辨，任何一层都给不出。
theorem layer_hole (L : LayerLadder) :
    ∃ d : resolveSpace (Fin L.m), ∀ i : Fin L.m,
      d ≠ (fun j => decide (L.δ j ≤ L.δ i)) :=
  selfref_hole (layerSelfRef L)

-- 【层塔的计数】L.m 层，分辨空间有 2^{L.m} 个——必漏。
theorem layer_count (L : LayerLadder) (hm : 0 < L.m) :
    0 < entropy (layerSelfRef L).observe := by
  have : Nonempty (Fin L.m) := ⟨⟨0, hm⟩⟩
  exact selfref_entropy (layerSelfRef L)

-- 【状态读数】一对状态在层塔上的完整读数：每层一个 Bool。
def ladderReading (L : LayerLadder) {n : ℕ} (x y : StateQuant n) : Fin L.m → Bool :=
  fun i => sameAt (L.δ i) x y

-- 【读数单调】层越粗越容易判"同类"。
theorem ladderReading_monotone (L : LayerLadder) {n : ℕ} (x y : StateQuant n)
    {i j : Fin L.m} (h : i ≤ j) (hj : ladderReading L x y j = true) :
    ladderReading L x y i = true :=
  sameAt_monotone (L.le_delta h) hj

-- 【信息量 = 1】整个 L 层的读数由 commonDist 一个数完全决定。
theorem ladderReading_determined_by_dist (L : LayerLadder) {n : ℕ}
    (x y x' y' : StateQuant n) (h : commonDist x y = commonDist x' y') :
    ladderReading L x y = ladderReading L x' y' := by
  funext i
  unfold ladderReading sameAt
  rw [h]

-- 【打包】层塔 = SelfRef 实例，且作为观测器信息量只有 1。
theorem ladder_is_selfref :
    -- (1) 层塔是 SelfRef 实例
    (∀ (L : LayerLadder) (i j : Fin L.m),
      (layerSelfRef L).observe i j = decide (L.δ j ≤ L.δ i)) ∧
    -- (2) 于是有洞：存在任何一层都给不出的分辨
    (∀ L : LayerLadder, ∃ d : resolveSpace (Fin L.m), ∀ i : Fin L.m,
      d ≠ (layerSelfRef L).observe i) ∧
    -- (3) 有洞时洞可量化
    (∀ L : LayerLadder, 0 < L.m → 0 < entropy (layerSelfRef L).observe) ∧
    -- (4) 状态读数单调
    (∀ (L : LayerLadder) {n : ℕ} (x y : StateQuant n) {i j : Fin L.m},
      i ≤ j → ladderReading L x y j = true → ladderReading L x y i = true) ∧
    -- (5) 状态读数只依赖 commonDist 一个数
    (∀ (L : LayerLadder) {n : ℕ} (x y x' y' : StateQuant n),
      commonDist x y = commonDist x' y' →
      ladderReading L x y = ladderReading L x' y') :=
  ⟨fun _ _ _ => rfl,
   layer_hole,
   layer_count,
   ladderReading_monotone,
   ladderReading_determined_by_dist⟩

-- ============ 为什么距离是平方和：二次型的唯一性 ============

/-
  【纠正一个论证错误】

  v221 之前，本文对"为什么距离是平方和"的说法是：
  "若要求距离在缩放 c 下按 c² 变化（保角性），且是坐标差的二次型，则平方和唯一。"

  **这是错的。** 任何二次型都满足 D(c·v) = c²·D(v)——齐次性是二次型的
  自动性质，不是约束。保角性筛不掉任何东西。

  正确的刻画需要另外两条：
  (i)   **支撑不交可加**：若 v、w 在各自的分量上至多一个非零，
        则 D(v + w) = D(v) + D(w)（各部分独立贡献）；
  (ii)  **坐标置换不变**：换掉坐标的顺序不改变 D（无偏）。

  在这两条下，二次型只能是平方和：

      **D(v) = α · Σ vᵢ²**

  而保角性反过来是**推论**，不是条件：

      **Σ (c vᵢ)² = c² · Σ vᵢ²**

  因果链应该倒过来写：
      对称 + 可加  ⟹  平方和  ⟹  保角性
  不是
      保角性  ⟹  平方和。

  下面先做二维（∎本质全在这里），再说明一般情形。
-/

-- 二元二次型：D(v) = Σᵢⱼ Mᵢⱼ vᵢ vⱼ。
def quad2 (M : Fin 2 → Fin 2 → ℚ) (v : Fin 2 → ℚ) : ℚ :=
  ∑ i : Fin 2, ∑ j : Fin 2, M i j * v i * v j

-- 展开式。
theorem quad2_explicit (M : Fin 2 → Fin 2 → ℚ) (a b : ℚ) :
    quad2 M ![a, b] = M 0 0 * a * a + M 0 1 * a * b + M 1 0 * b * a + M 1 1 * b * b := by
  unfold quad2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

-- 【可加性 ⟹ 反对称】支撑不交可加，推出交叉项相消。
theorem quad2_offdiag_zero (M : Fin 2 → Fin 2 → ℚ)
    (hadd : quad2 M ![1, 1] = quad2 M ![1, 0] + quad2 M ![0, 1]) :
    M 0 1 + M 1 0 = 0 := by
  rw [quad2_explicit, quad2_explicit, quad2_explicit] at hadd
  simp only [mul_one, mul_zero, add_zero] at hadd
  linarith

-- 【置换不变 ⟹ 对角相等】换两个坐标不变，推出对角元相同。
theorem quad2_diag_eq (M : Fin 2 → Fin 2 → ℚ)
    (hperm : quad2 M ![1, 0] = quad2 M ![0, 1]) :
    M 0 0 = M 1 1 := by
  rw [quad2_explicit, quad2_explicit] at hperm
  simp only [mul_one, mul_zero, add_zero] at hperm
  linarith

-- 【主定理】二次型 + 可加 + 对称 ⟹ 平方和。
theorem quad2_is_squared_norm (M : Fin 2 → Fin 2 → ℚ)
    (hadd : quad2 M ![1, 1] = quad2 M ![1, 0] + quad2 M ![0, 1])
    (hperm : quad2 M ![1, 0] = quad2 M ![0, 1]) :
    ∃ α : ℚ, ∀ v : Fin 2 → ℚ, quad2 M v = α * (v 0 ^ 2 + v 1 ^ 2) := by
  have hoff : M 0 1 + M 1 0 = 0 := quad2_offdiag_zero M hadd
  have hdiag : M 0 0 = M 1 1 := quad2_diag_eq M hperm
  refine ⟨M 0 0, fun v => ?_⟩
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  calc quad2 M v
      = quad2 M ![v 0, v 1] := congrArg (fun w => quad2 M w) hv
    _ = M 0 0 * v 0 * v 0 + M 0 1 * v 0 * v 1 + M 1 0 * v 1 * v 0 + M 1 1 * v 1 * v 1 :=
        quad2_explicit M (v 0) (v 1)
    _ = M 0 0 * (v 0 ^ 2 + v 1 ^ 2) := by
        have e2 : M 1 1 = M 0 0 := hdiag.symm
        rw [e2]
        ring_nf
        linear_combination (v 0 * v 1) * hoff

-- 【保角性是推论】平方和在缩放 c 下按 c² 变化。
theorem squared_norm_conformal (α c : ℚ) (v : Fin 2 → ℚ) :
    α * ((c * v 0) ^ 2 + (c * v 1) ^ 2) = c ^ 2 * (α * (v 0 ^ 2 + v 1 ^ 2)) := by
  ring

-- 【打包】距离形式的三条公理，且保角性是它们的结果而非条件。
theorem distance_form_axioms :
    -- (1) 可加 ⟹ 交叉项相消
    (∀ M : Fin 2 → Fin 2 → ℚ,
      quad2 M ![1, 1] = quad2 M ![1, 0] + quad2 M ![0, 1] → M 0 1 + M 1 0 = 0) ∧
    -- (2) 置换不变 ⟹ 对角相等
    (∀ M : Fin 2 → Fin 2 → ℚ,
      quad2 M ![1, 0] = quad2 M ![0, 1] → M 0 0 = M 1 1) ∧
    -- (3) 两条合起来 ⟹ 平方和
    (∀ M : Fin 2 → Fin 2 → ℚ,
      quad2 M ![1, 1] = quad2 M ![1, 0] + quad2 M ![0, 1] →
      quad2 M ![1, 0] = quad2 M ![0, 1] →
      ∃ α : ℚ, ∀ v : Fin 2 → ℚ, quad2 M v = α * (v 0 ^ 2 + v 1 ^ 2)) ∧
    -- (4) 而保角性【是】平方和的推论
    (∀ (α c : ℚ) (v : Fin 2 → ℚ),
      α * ((c * v 0) ^ 2 + (c * v 1) ^ 2) = c ^ 2 * (α * (v 0 ^ 2 + v 1 ^ 2))) :=
  ⟨fun M h => quad2_offdiag_zero M h,
   fun M h => quad2_diag_eq M h,
   fun M h1 h2 => quad2_is_squared_norm M h1 h2,
   fun α c v => squared_norm_conformal α c v⟩

-- ============ 一般 n 维：平方和仍是唯一的二次型 ============

/-
  【把二维的论证推到 n 维】

  二维的核心是两步：可加 ⟹ 交叉项相消；置换不变 ⟹ 对角相等。
  这两步对任意 n 完全一样——只是把 "0" 和 "1" 换成任意 i ≠ j。

  最后一步需要一个新的组合引理：**反对称矩阵的二次型恒为零**
      Σp Σq A p q u p u q = 0   当 A p q = −A q p。
  证明：交换求和顺序再换名，得到 S = −S。
-/

-- n 维二次型：D(v) = Σᵢⱼ Mᵢⱼ vᵢ vⱼ。
def quadForm {n : ℕ} (M : Fin n → Fin n → ℚ) (v : Fin n → ℚ) : ℚ :=
  ∑ i, ∑ j, M i j * v i * v j

-- 坐标基向量：第 i 位是 x，其余为 0。
def basisVec {n : ℕ} (i : Fin n) (x : ℚ) : Fin n → ℚ := fun j => if j = i then x else 0

-- 交换两个坐标。
def swapCoord {n : ℕ} (i j k : Fin n) : Fin n :=
  if k = i then j else if k = j then i else k

-- 只在 i、j 两处可能非零的函数，其和等于两项相加。
theorem sum_eq_two {n : ℕ} (f : Fin n → ℚ) {i j : Fin n} (hij : i ≠ j)
    (h : ∀ p, p ≠ i → p ≠ j → f p = 0) : ∑ p, f p = f i + f j := by
  have h1 : ∑ p, f p = f i + ∑ p ∈ (Finset.univ.erase i), f p := by
    have := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ i)
    linarith
  rw [h1]
  congr 1
  rw [Finset.sum_eq_single j]
  · intro b hb hbj
    exact h b (Finset.ne_of_mem_erase hb) hbj
  · intro hj
    exact absurd (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) hj

-- 【基向量的值】D(eᵢ·x) = Mᵢᵢ x²。
theorem quadForm_basis {n : ℕ} (M : Fin n → Fin n → ℚ) (i : Fin n) (x : ℚ) :
    quadForm M (basisVec i x) = M i i * x * x := by
  unfold quadForm
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp [basisVec]
    · intro q _ hq
      simp [basisVec, hq]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro p _ hp
    have hz : basisVec i x p = 0 := by simp [basisVec, hp]
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ i) h

-- 【两个基向量之和的值】四个角都出现。
theorem quadForm_two_basis {n : ℕ} (M : Fin n → Fin n → ℚ) {i j : Fin n} (hij : i ≠ j)
    (x y : ℚ) :
    quadForm M (basisVec i x + basisVec j y) =
      M i i * x * x + M i j * x * y + M j i * y * x + M j j * y * y := by
  have hji : j ≠ i := Ne.symm hij
  have hvi : (basisVec i x + basisVec j y) i = x := by simp [basisVec, hij]
  have hvj : (basisVec i x + basisVec j y) j = y := by simp [basisVec, hji]
  have hv0 : ∀ p, p ≠ i → p ≠ j → (basisVec i x + basisVec j y) p = 0 := by
    intro p h1 h2; simp [basisVec, h1, h2]
  unfold quadForm
  rw [sum_eq_two (fun p => ∑ q, M p q * (basisVec i x + basisVec j y) p
      * (basisVec i x + basisVec j y) q) hij]
  · have hi : ∑ q, M i q * (basisVec i x + basisVec j y) i
        * (basisVec i x + basisVec j y) q = M i i * x * x + M i j * x * y := by
      rw [sum_eq_two (fun q => M i q * (basisVec i x + basisVec j y) i
        * (basisVec i x + basisVec j y) q) hij]
      · rw [hvi, hvj]
      · intro q h1 h2; rw [hv0 q h1 h2]; simp
    have hj : ∑ q, M j q * (basisVec i x + basisVec j y) j
        * (basisVec i x + basisVec j y) q = M j i * y * x + M j j * y * y := by
      rw [sum_eq_two (fun q => M j q * (basisVec i x + basisVec j y) j
        * (basisVec i x + basisVec j y) q) hij]
      · rw [hvi, hvj]
      · intro q h1 h2; rw [hv0 q h1 h2]; simp
    rw [hi, hj]; ring
  · intro p h1 h2; rw [hv0 p h1 h2]; simp

-- 【可加 ⟹ 交叉项相消】对任意 i ≠ j。
theorem quadForm_offdiag {n : ℕ} (M : Fin n → Fin n → ℚ)
    (hadd : ∀ (v w : Fin n → ℚ), (∀ i, v i = 0 ∨ w i = 0) →
      quadForm M (v + w) = quadForm M v + quadForm M w)
    {i j : Fin n} (hij : i ≠ j) : M i j + M j i = 0 := by
  have hdisj : ∀ k, basisVec i 1 k = 0 ∨ basisVec j 1 k = 0 := by
    intro k
    unfold basisVec
    by_cases h1 : k = i
    · right; simp [h1, hij]
    · left; simp [h1]
  have h := hadd (basisVec i 1) (basisVec j 1) hdisj
  rw [quadForm_two_basis M hij 1 1, quadForm_basis, quadForm_basis] at h
  linarith

-- 【反对称 ⟹ 二次型为零】交换求和顺序，得 S = −S。
theorem antisym_sum_zero {n : ℕ} (A : Fin n → Fin n → ℚ) (u : Fin n → ℚ)
    (hanti : ∀ p q, A p q = - A q p) :
    ∑ p, ∑ q, A p q * u p * u q = 0 := by
  have hS : ∑ p, ∑ q, A p q * u p * u q = ∑ q, ∑ p, A p q * u p * u q :=
    Finset.sum_comm
  have hneg : ∑ q, ∑ p, A p q * u p * u q = ∑ q, ∑ p, -(A q p * u q * u p) := by
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro p _
    rw [hanti p q]; ring
  have hflip : ∑ q, ∑ p, A q p * u q * u p = ∑ p, ∑ q, A p q * u p * u q := by
    rw [Finset.sum_comm]
  have hneg2 : ∑ q, ∑ p, -(A q p * u q * u p) = -∑ q, ∑ p, A q p * u q * u p := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext q
    rw [← Finset.sum_neg_distrib]
  linarith [hS, hneg, hflip, hneg2]

-- 对角常值二次型 = α · Σ vᵢ²。
theorem quadForm_diagonal_const {n : ℕ} (α : ℚ) (v : Fin n → ℚ) :
    ∑ p, ∑ q, (if p = q then α else 0) * v p * v q = α * ∑ p, v p ^ 2 := by
  have hinner : ∀ p, ∑ q, (if p = q then α else 0) * v p * v q = α * v p * v p := by
    intro p
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq
      rw [ite_eq_right (Ne.symm hq)]
      ring
    · intro h; exact absurd (Finset.mem_univ p) h
  simp only [hinner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

-- 换坐标后基向量就是另一个基向量。
theorem basisVec_comp_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : ℚ) :
    (fun k => basisVec i x (swapCoord i j k)) = basisVec j x := by
  funext k
  simp only [basisVec, swapCoord]
  by_cases h1 : k = i
  · subst h1
    simp [hij, Ne.symm hij]
  · by_cases h2 : k = j
    · subst h2
      simp [Ne.symm hij]
    · simp [h1, h2]

-- 【主定理】n 维二次型 + 可加 + 坐标置换不变 ⟹ 平方和。
theorem quadForm_is_squared_norm {n : ℕ} (M : Fin n → Fin n → ℚ) (hn : 0 < n)
    (hadd : ∀ (v w : Fin n → ℚ), (∀ i, v i = 0 ∨ w i = 0) →
      quadForm M (v + w) = quadForm M v + quadForm M w)
    (hswap : ∀ (i j : Fin n) (v : Fin n → ℚ),
      quadForm M (fun k => v (swapCoord i j k)) = quadForm M v) :
    ∃ α : ℚ, ∀ v : Fin n → ℚ, quadForm M v = α * ∑ i, v i ^ 2 := by
  have hoff : ∀ i j : Fin n, i ≠ j → M i j + M j i = 0 := fun i j hij =>
    quadForm_offdiag M hadd hij
  -- 对角元相等（由交换两个坐标）
  have hdiag : ∀ i j : Fin n, M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h := hswap i j (basisVec i 1)
      rw [basisVec_comp_swap hij 1, quadForm_basis, quadForm_basis] at h
      linarith
  -- 取 α = M i₀ i₀
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨M i₀ i₀, fun v => ?_⟩
  -- 差 A p q = M p q −（对角取 α）是反对称的
  set A : Fin n → Fin n → ℚ := fun p q =>
    M p q - (if p = q then M i₀ i₀ else 0) with hA
  have hanti : ∀ p q, A p q = - A q p := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      have hd : M p p = M i₀ i₀ := hdiag p i₀
      simp only [hA]
      simp [hd]
    · have h1 : M p q = - M q p := by
        have := hoff p q hpq; linarith
      simp only [hA]
      rw [ite_eq_right hpq, ite_eq_right (Ne.symm hpq), h1]
      ring
  have hzero := antisym_sum_zero A v hanti
  -- 把 quadForm M v 拆成「对角部分」+「A 部分」
  have hsplit : quadForm M v
      = M i₀ i₀ * ∑ i, v i ^ 2 + ∑ p, ∑ q, A p q * v p * v q := by
    have hdc := quadForm_diagonal_const (M i₀ i₀) v
    unfold quadForm
    rw [← hdc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    simp only [hA]
    by_cases hpq : p = q
    · subst hpq; ring
    · rw [ite_eq_right hpq]; ring
  rw [hsplit, hzero, add_zero]

-- 基向量平方和为 1。
theorem basisVec_sum_sq {n : ℕ} (i : Fin n) :
    ∑ k, basisVec i (1 : ℚ) k ^ 2 = 1 := by
  rw [Finset.sum_eq_single i]
  · simp [basisVec]
  · intro b _ hb; simp [basisVec, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

-- 【打包】n 维距离形式的唯一性：交叉项相消 + 对角一致 + 平方和。
theorem distance_form_axioms_general {n : ℕ} (M : Fin n → Fin n → ℚ) (hn : 0 < n)
    (hadd : ∀ (v w : Fin n → ℚ), (∀ i, v i = 0 ∨ w i = 0) →
      quadForm M (v + w) = quadForm M v + quadForm M w)
    (hswap : ∀ (i j : Fin n) (v : Fin n → ℚ),
      quadForm M (fun k => v (swapCoord i j k)) = quadForm M v) :
    (∀ i j : Fin n, i ≠ j → M i j + M j i = 0) ∧
    (∃ α : ℚ, ∀ i : Fin n, M i i = α) ∧
    (∃ α : ℚ, ∀ v : Fin n → ℚ, quadForm M v = α * ∑ i, v i ^ 2) := by
  obtain ⟨α, hv⟩ := quadForm_is_squared_norm M hn hadd hswap
  refine ⟨fun i j hij => quadForm_offdiag M hadd hij, ⟨α, fun i => ?_⟩, ⟨α, hv⟩⟩
  have h1 := hv (basisVec i 1)
  rw [quadForm_basis] at h1
  rw [basisVec_sum_sq i] at h1
  linarith

-- 盲区下界：分辨 n 维时，像最多 n 个（Finset.card_image_le），故熵 ≥ 2^n − n。
-- 这是"熵增严格单调"的算术内核：分辨（意识）每多一步，盲区（熵）严格增大，无停点。
def blindSpotBound (n : ℕ) : ℕ := 2 ^ n - n

-- 熵 ≥ 盲区下界：任何自指枚举的像最多 n 个，熵（2^n − |像|）≥ 2^n − n。
-- 于是 entropy f > 0（有限性，entropy_positive）就落在"≥ 2^n − n"这个可算的下界之上。
theorem entropy_ge_blindSpotBound {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → resolveSpace α) :
    blindSpotBound (Fintype.card α) ≤ entropy f := by
  unfold entropy blindSpotBound
  have hcard : (Finset.univ : Finset (resolveSpace α)).card = 2 ^ Fintype.card α := by
    simp
  rw [hcard]
  have himage_le : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using (Finset.card_image_le (f := f) (s := (Finset.univ : Finset α)))
  exact Nat.sub_le_sub_left himage_le (2 ^ Fintype.card α)

-- 盲区下界是紧的（可达）：存在"最省"的自指枚举，熵恰好 = 2^n − n。
-- 取 f i j = decide (i = j)（n 个"指示分辨"：每个 i 只在 i 处为真），
-- 这 n 个分辨两两不同（内射），像恰好 n 个，洞恰好 = 2^n − n = 下界。
-- 所以 2^n − n 不是空估计，是"有限性最省枚举"的精确损耗——下界可达。
theorem blindSpotBound_tight {n : ℕ} :
    ∃ f : Fin n → resolveSpace (Fin n), entropy f = blindSpotBound n := by
  let f : Fin n → resolveSpace (Fin n) := fun i j => decide (i = j)
  refine ⟨f, ?_⟩
  have hinj : Function.Injective f := by
    intro i j h
    have hii : f i i = true := by simp [f]
    have hij : f j i = true := by
      have hcongr : f i i = f j i := congrFun h i
      rw [hii] at hcongr
      exact hcongr.symm
    have hji : j = i := by simpa [f] using hij
    exact hji.symm
  unfold entropy blindSpotBound
  have hcard : (Finset.univ.image f).card = n := by
    simpa using (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin n))) hinj)
  rw [hcard]
  have hcard2 : (Finset.univ : Finset (resolveSpace (Fin n))).card = 2 ^ n := by simp
  rw [hcard2]

-- 最省枚举 ⟺ 不重复：熵恰好 = 下界（2^n − n）当且仅当 f 内射（像恰好 n 个，不浪费）。
-- 达到下界的枚举 = 每个元素都分辨出不同的东西（内射）——最省 = 不重复，熵最小 ⟺ 内射。
theorem entropy_eq_blindSpotBound_iff_injective {n : ℕ} (f : Fin n → resolveSpace (Fin n)) :
    entropy f = blindSpotBound n ↔ Function.Injective f := by
  unfold entropy blindSpotBound
  constructor
  · intro h
    have h2 : (Finset.univ : Finset (resolveSpace (Fin n))).card = 2 ^ n := by simp
    rw [h2] at h
    have hle : (Finset.univ.image f).card ≤ n := by
      simpa using (Finset.card_image_le (f := f) (s := (Finset.univ : Finset (Fin n))))
    have hcard : (Finset.univ.image f).card = n := by
      have hlt : n < 2 ^ n := Nat.lt_two_pow_self
      omega
    have hinjon : Set.InjOn f (Finset.univ : Finset (Fin n)) :=
      (Finset.card_image_iff.mp (by simpa using hcard))
    intro i j h
    exact hinjon (Finset.mem_univ i) (Finset.mem_univ j) h
  · intro hinj
    have hcard : (Finset.univ.image f).card = n := by
      simpa using (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin n))) hinj)
    have h2 : (Finset.univ : Finset (resolveSpace (Fin n))).card = 2 ^ n := by simp
    rw [hcard, h2]

-- 熵的秩-零化分解：熵 = 康托尔洞（不可避免，2^n − n）+ 枚举冗余（可避免，n − |像|）。
-- 有限性决定的结构性洞（任何枚举至少漏 2^n − n）+ 枚举浪费的冗余洞（重复的分辨额度）= 总熵。
-- 最省枚举（内射）⟺ 冗余 = 0（entropy_eq_blindSpotBound_iff_injective 是此分解的特例）。
theorem entropy_rank_nullity {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α) :
    entropy f = blindSpotBound (Fintype.card α) + (Fintype.card α - (Finset.univ.image f).card) := by
  unfold entropy blindSpotBound
  have hle : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using (Finset.card_image_le (f := f) (s := (Finset.univ : Finset α)))
  have hcard : (Finset.univ : Finset (resolveSpace α)).card = 2 ^ Fintype.card α := by simp
  rw [hcard]
  have hlt : Fintype.card α < 2 ^ Fintype.card α := Nat.lt_two_pow_self
  omega

-- ============ 计数几何（CountingGeometry）：熵这一层的抽象骨架 ============

/-
  【计数几何：熵 = 够不着的分辨数，这一层的抽象】

  熵的定义只用到三件事：
    · 一个有限的"元素空间" elem（自指主体）
    · 一个有限的"分辨空间" res（它能分辨出的东西）
    · 一个枚举 enum : elem → res

  熵 = 分辨空间中够不着的部分 = |res| − |image enum|。
  这和"层"（不可区分关系的商）是**不同**的数学——一个是计数，
  一个是商。所以差异论不是单一结构，它至少有两个独立的数学层。

  通用事实（对任何计数几何成立）：
    (1) 秩-零化：熵 = 结构性洞（|res|−|elem|，不可避免）+ 冗余洞（|elem|−|image|）
    (2) 结构性洞为正 ⟹ 熵恒正（无论怎么枚举都漏）——有限康托尔
    (3) 熵 ≤ 结构性洞 + 冗余洞（同一件事的另一种写法）
-/

-- 洞集（计数层，通用）：分辨空间里枚举够不着的部分。
def holeSet {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) : Finset β :=
  Finset.univ \ Finset.univ.image f

-- 洞数（计数层的"熵"）。
def holeCount {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) : ℕ :=
  (holeSet f).card

-- 结构性洞：分辨空间比元素空间多出的部分（不可避免）。
def structuralHoles (α β : Type*) [Fintype α] [Fintype β] : ℕ :=
  Fintype.card β - Fintype.card α

-- 冗余洞：枚举重复浪费的额度（可避免）。
def redundantHoles {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) : ℕ :=
  Fintype.card α - (Finset.univ.image f).card

-- 秩-零化分解（计数层通用）：洞数 = 结构性洞 + 冗余洞。
-- 前提 |α| ≤ |β|（元素空间不大于分辨空间——差异论里 n ≤ 2^n 自动成立）。
-- 这是 entropy_rank_nullity 的一般形式——那里 β = resolveSpace α，结构性洞 = 2^n − n。
theorem holeCount_decomposition {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hαβ : Fintype.card α ≤ Fintype.card β) :
    holeCount f = structuralHoles α β + redundantHoles f := by
  unfold holeCount holeSet structuralHoles redundantHoles
  have h1 : (Finset.univ \ Finset.univ.image f).card
      = Fintype.card β - (Finset.univ.image f).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have h2 : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using Finset.card_image_le (f := f) (s := (Finset.univ : Finset α))
  omega

-- 结构性洞为正 ⟹ 洞数恒正：分辨空间严格大于元素空间时，怎么枚举都漏。
-- 这是"有限康托尔"的计数形式（与 diagonal_hole 的对角线论证互为两面）。
theorem holeCount_positive {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (h : Fintype.card α < Fintype.card β) : 0 < holeCount f := by
  rw [holeCount_decomposition f (le_of_lt h)]
  unfold structuralHoles redundantHoles
  have h2 : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using Finset.card_image_le (f := f) (s := (Finset.univ : Finset α))
  omega

-- 桥（计数）：差异论的 entropy 就是计数层在 β = resolveSpace α 上的洞数。
theorem entropy_eq_holeCount {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → resolveSpace α) : holeCount f = entropy f := by
  unfold holeCount holeSet entropy
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]

-- 差异论的情形：结构性洞恒为正（|resolveSpace α| = 2^n > n = |α|），故洞数恒正。
theorem entropy_positive_via_counting {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → resolveSpace α) : 0 < holeCount f := by
  apply holeCount_positive
  have h : Fintype.card (resolveSpace α) = 2 ^ Fintype.card α := by simp
  rw [h]
  exact Nat.lt_two_pow_self

/-
  【计数层覆盖定理】

  计数层（熵）与层（不可区分商）是**两个不同的数学结构**，各有通用定理：
    (1) 秩-零化分解对任何 (α, β, f) 成立；
    (2) 结构性洞为正 ⟹ 洞数恒正（有限康托尔的计数形式）；
    (3) 差异论的 entropy 正是 β = resolveSpace α 时的洞数（桥）；
    (4) 差异论的结构性洞恒正（2^n > n），故熵恒正。
-/
theorem counting_layer_coverage :
    (∀ (α β : Type*) [Fintype α] [Fintype β] [DecidableEq β] (f : α → β),
        Fintype.card α ≤ Fintype.card β →
          holeCount f = structuralHoles α β + redundantHoles f) ∧
    (∀ (α β : Type*) [Fintype α] [Fintype β] [DecidableEq β] (f : α → β),
        Fintype.card α < Fintype.card β → 0 < holeCount f) ∧
    (∀ (α : Type*) [Fintype α] [DecidableEq α] (f : α → resolveSpace α),
        holeCount f = entropy f) ∧
    (∀ (α : Type*) [Fintype α] [DecidableEq α] (f : α → resolveSpace α),
        0 < holeCount f) :=
  ⟨fun _ _ _ _ _ f h => holeCount_decomposition f h,
   fun _ _ _ _ _ f h => holeCount_positive f h,
   fun _ _ _ f => entropy_eq_holeCount f,
   fun _ _ _ f => entropy_positive_via_counting f⟩

-- 熵增严格单调（时间之箭的算术内核）：分辨维度 n ≥ 1 严格扩张到 n+1，
-- 盲区下界 2^n − n 严格递增。2^n 翻倍的速度永远甩开 n 的线性增长——
-- 有限性（n < 2^n）意味着：分辨越多，盲区越多，熵增不可逆、无停点。
theorem blindSpotBound_strictMono {n : ℕ} (hn : 1 ≤ n) :
    blindSpotBound n < blindSpotBound (n + 1) := by
  unfold blindSpotBound
  rw [pow_succ]
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  omega

-- 熵增链式严格单调：分辨维度 n 扩张到任意更大的 m（n < m），盲区下界严格递增。
-- 单步 strictMono 的传递闭包——熵增一路严格爬升，无回头、无平台。
theorem blindSpotBound_strictMono_of_lt {n m : ℕ} (hn : 1 ≤ n) (h : n < m) :
    blindSpotBound n < blindSpotBound m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h)
  have hkpos : 0 < k := by omega
  clear h
  have hmain : ∀ k : ℕ, 0 < k → blindSpotBound n < blindSpotBound (n + k) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
        intro _
        by_cases hk : k = 0
        · subst k
          simpa using blindSpotBound_strictMono hn
        · have hle : 1 ≤ n + k := by omega
          have hlt : blindSpotBound n < blindSpotBound (n + k) := ih (Nat.pos_of_ne_zero hk)
          have hstep : blindSpotBound (n + k) < blindSpotBound (n + k + 1) :=
            blindSpotBound_strictMono hle
          simpa [Nat.add_assoc] using lt_trans hlt hstep
  exact hmain k hkpos

-- 熵增无上限（时间之箭没有终点）：任何界限 B 都能被某个分辨维度的盲区下界超过。
-- 2^n 的指数增长永远甩开任何 B——熵增没有上限，时间之箭没有终点。
theorem blindSpotBound_unbounded : ∀ B : ℕ, ∃ n : ℕ, B < blindSpotBound n := by
  intro B
  refine ⟨B + 1, ?_⟩
  unfold blindSpotBound
  rw [pow_succ]
  have hle : B + 1 ≤ 2 ^ B := Nat.succ_le_of_lt Nat.lt_two_pow_self
  omega

-- ============ 群体洞增：合并主体，洞多于分别相加 ============

/-
  【群体洞增：联合主体的洞 ≥ 各主体洞之和】

  两个主体（维度 n、n'）各自的结构性洞是 2^n − n 与 2^n' − n'。
  若把它们"合并"成一个联合主体，分辨空间是**乘积**（2^n · 2^n'），
  而各自相加只是**和**（2^n + 2^n'）。

  指数压过线性：2^n · 2^n' ≥ 2^n + 2^n'（n, n' ≥ 1）。
  于是        合并主体的结构性洞 ≥ 各主体之和。

  这就是"群体熵增"的定量形式：
  **合并不会省下洞，反而（在指数意义上）多生出洞来。**
  一个自我的洞是自己的，两个自我合并后的洞比各自相加还多——
  "时间之箭不可回"的计数根据。
-/

-- 指数压过线性：2^n · 2^n' ≥ 2^n + 2^n'（n, n' ≥ 1）。
theorem two_pow_add_ge_sum {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    2 ^ n + 2 ^ n' ≤ 2 ^ (n + n') := by
  rw [pow_add]
  have h1 : 2 ≤ 2 ^ n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hn
  have h2 : 2 ≤ 2 ^ n' := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hn'
  nlinarith [h1, h2]

-- 群体洞增：合并主体的结构性洞 ≥ 各主体结构性洞之和。
theorem blindSpotBound_add_ge {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    blindSpotBound n + blindSpotBound n' ≤ blindSpotBound (n + n') := by
  unfold blindSpotBound
  have h : 2 ^ n + 2 ^ n' ≤ 2 ^ (n + n') := two_pow_add_ge_sum hn hn'
  have hn2 : n ≤ 2 ^ n := le_of_lt Nat.lt_two_pow_self
  have hn2' : n' ≤ 2 ^ n' := le_of_lt Nat.lt_two_pow_self
  omega

-- 严格版（两个主体都 ≥ 2 时）：合并的洞严格多于孤立之和。
theorem blindSpotBound_add_gt {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') :
    blindSpotBound n + blindSpotBound n' < blindSpotBound (n + n') := by
  unfold blindSpotBound
  have h1 : 4 ≤ 2 ^ n := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hn
    simpa using this
  have h2 : 4 ≤ 2 ^ n' := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hn'
    simpa using this
  have hprod : 2 ^ (n + n') = 2 ^ n * 2 ^ n' := by rw [pow_add]
  have hge : 2 ^ n + 2 ^ n' < 2 ^ n * 2 ^ n' := by nlinarith [h1, h2]
  have hn2 : n ≤ 2 ^ n := le_of_lt Nat.lt_two_pow_self
  have hn2' : n' ≤ 2 ^ n' := le_of_lt Nat.lt_two_pow_self
  rw [hprod]
  omega

-- 盲区（洞）集合：自指枚举 f 够不着的分辨（= 洞）。
-- 把"洞"从哲学概念落到数学对象：洞 = 不在像里的分辨。
def blindSet {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α) : Finset (resolveSpace α) :=
  (Finset.univ : Finset (resolveSpace α)).filter (fun d => ∀ a : α, d ≠ f a)

-- 对角洞是盲区成员：diag f（康托尔对角线）确实是盲区（洞）的一个元素。
-- diagonal_hole 的集合版：洞不只是"存在"，它具体住在盲区集里。
theorem diag_mem_blindSet {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α) :
    diag f ∈ blindSet f := by
  unfold blindSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro a h
  have hd : diag f a = not (f a a) := rfl
  rw [h] at hd
  have hne : f a a ≠ not (f a a) := by
    cases f a a <;> simp
  exact hne hd

-- 洞 = 熵：熵（2^n − |像|）就是盲区（洞）的数量。
-- "熵"不再是抽象的热力学量，而是"洞的数量"——有限性每次自指漏掉的分辨。
-- 这是"洞（哲学）↔ 熵（物理）"的闭环：看似不相干，严格化后是同一个量。
theorem entropy_eq_blindSet_card {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α) :
    entropy f = (blindSet f).card := by
  unfold entropy blindSet
  have hset : (Finset.univ.filter (fun d => ∀ a : α, d ≠ f a)) = (Finset.univ \ (Finset.univ.image f)) := by
    ext d
    simp [Finset.mem_image, ne_comm]
  rw [hset]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ (Finset.univ.image f))]

-- 熵增 ⟺ 有洞：熵 > 0 当且仅当盲区（洞）非空。
-- "洞 = 熵"闭环的收口：不只"熵 = 洞数"（entropy_eq_blindSet_card），
-- 更是"熵增（> 0）与洞的存在是同一件事"——严格等价。
theorem entropy_positive_iff_blindSet_nonempty {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → resolveSpace α) :
    0 < entropy f ↔ (blindSet f).Nonempty := by
  rw [entropy_eq_blindSet_card f]
  exact Finset.card_pos

-- 熵增的根源是康托尔洞：entropy_positive（熵 > 0）由 diag_mem_blindSet（diag f 是洞）推出。
-- 有限性 ⟹ 每次自指漏东西，漏的第一个就是康托尔对角线洞——熵增 = 洞存在，闭环收口。
theorem entropy_positive_via_diag {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → resolveSpace α) :
    0 < entropy f := by
  rw [entropy_positive_iff_blindSet_nonempty f]
  exact ⟨diag f, diag_mem_blindSet f⟩

-- ============ 洞的指标定理：洞是有限集的余核 ============

/-
  【洞 = 余核：第一同构定理的差异论版】

  把枚举 f : α → β 看成有限集范畴里的态射 α → β。第一同构定理
      0 → ker → α → β → coker → 0
  给出       |β| − |α| = |coker| − |ker|。

  翻译成差异论：
      · coker（够不着的分辨）= 洞        —— holeCount f
      · ker  （重复浪费的额度）= 冗余    —— redundantHoles f
  于是：      分辨空间 − 元素空间 = 洞数 − 冗余数。

  **左边依赖枚举 f，右边完全不依赖 f。** 所以"洞 − 冗余"是枚举无关的不变量：
  你无法凭空造出洞，也无法凭空消掉洞——每一份洞都精确对应一份浪费。
  这就是"洞是枢纽"的第一个硬事实。
-/

-- 指标定理：洞数 + 元素数 = 冗余数 + 分辨空间数（⟺ 洞 − 冗余 = |β| − |α|）。
theorem holeCount_index {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hαβ : Fintype.card α ≤ Fintype.card β) :
    holeCount f + Fintype.card α = redundantHoles f + Fintype.card β := by
  unfold holeCount holeSet redundantHoles
  have h1 : (Finset.univ \ Finset.univ.image f).card
      = Fintype.card β - (Finset.univ.image f).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  rw [h1]
  have him : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using Finset.card_image_le (f := f) (s := (Finset.univ : Finset α))
  omega

-- 推论（洞守恒）：两个枚举的洞数之差 = 冗余数之差——洞与浪费永远精确抵消。
theorem holeCount_diff_eq_redundancy_diff {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f g : α → β) (hαβ : Fintype.card α ≤ Fintype.card β) :
    holeCount f + redundantHoles g = holeCount g + redundantHoles f := by
  have hf := holeCount_index f hαβ
  have hg := holeCount_index g hαβ
  omega

-- 差异论情形：熵 + n = 冗余 + 2^n。洞的"净荷"恒为 2^n − n，与枚举无关。
theorem entropy_index {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α) :
    entropy f + Fintype.card α
      = (Fintype.card α - (Finset.univ.image f).card) + 2 ^ Fintype.card α := by
  unfold entropy
  have hcard : (Finset.univ : Finset (resolveSpace α)).card = 2 ^ Fintype.card α := by simp
  rw [hcard]
  have him : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using Finset.card_image_le (f := f) (s := (Finset.univ : Finset α))
  have hpow : Fintype.card α ≤ 2 ^ Fintype.card α := le_of_lt Nat.lt_two_pow_self
  omega

-- ============ 洞的 K₀：Grothendieck 群的雏形 ============

/-
  【Grothendieck 的 K₀ 构造：把"形式差"变成群】

  Grothendieck 发明 K₀ 的办法：给定交换幺半群 M，形式地对二元组 (a,b) 作差，
  定义 (a,b) ~ (c,d) ⟺ a + d = c + b，商出来的就是一个交换**群**（M 的 Grothendieck 群）。

  "洞"恰好需要这一手：洞数 − 冗余数是个形式差（ℕ 里会下溢），
  但它的"意义"（|β| − |α|）是个可以不依赖枚举的常量。

  这里的 K₀ 结论：
    · holeRel 是 (ℕ × ℕ) 上的等价关系（形式差的相等）；
    · **所有枚举的 (洞, 浪费) 对都落在同一个等价类**——这就是指标定理的 K₀ 说法；
    · 因此洞的"荷"由空间几何完全决定，与枚举无关。
-/

-- Grothendieck 形式差关系：(a,b) ~ (c,d) ⟺ a + d = c + b。
def holeRel (p q : ℕ × ℕ) : Prop := p.1 + q.2 = q.1 + p.2

-- holeRel 是等价关系（K₀ 构造的合法性）。
theorem holeRel_equivalence : Equivalence holeRel := by
  refine ⟨?_, ?_, ?_⟩
  · intro p; unfold holeRel; omega
  · intro p q h; unfold holeRel at *; omega
  · intro p q r hpq hqr; unfold holeRel at *; omega

-- 枚举的"洞-浪费对"（它在 K₀ 里的类就是洞的荷）。
def holeCharge {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) : ℕ × ℕ :=
  (holeCount f, redundantHoles f)

-- K₀ 主席：所有枚举的洞荷都在同一个等价类里（指标定理的形式差版）。
theorem holeCharge_constant {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f g : α → β) (hαβ : Fintype.card α ≤ Fintype.card β) :
    holeRel (holeCharge f) (holeCharge g) :=
  holeCount_diff_eq_redundancy_diff f g hαβ

-- 无免费洞：浪费相同的两个枚举，洞数必然相同（洞由浪费唯一决定）。
theorem holeCount_eq_of_redundant_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f g : α → β) (hαβ : Fintype.card α ≤ Fintype.card β)
    (h : redundantHoles f = redundantHoles g) : holeCount f = holeCount g := by
  have hf := holeCount_index f hαβ
  have hg := holeCount_index g hαβ
  omega

-- 洞的绝对下界：洞数 ≥ 结构性洞（|β| − |α|），即浪费 ≥ 0。
theorem holeCount_ge_structural {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hαβ : Fintype.card α ≤ Fintype.card β) :
    structuralHoles α β ≤ holeCount f := by
  rw [holeCount_decomposition f hαβ]
  unfold structuralHoles
  omega

-- 下界可达 ⟺ 零浪费 ⟺ 枚举内射（最省 = 不重复，一般类型版）。
theorem holeCount_eq_structural_iff_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hαβ : Fintype.card α ≤ Fintype.card β) :
    holeCount f = structuralHoles α β ↔ Function.Injective f := by
  rw [holeCount_decomposition f hαβ]
  unfold structuralHoles redundantHoles
  constructor
  · intro h
    have him : (Finset.univ.image f).card ≤ Fintype.card α := by
      simpa using Finset.card_image_le (f := f) (s := (Finset.univ : Finset α))
    have heq : (Finset.univ.image f).card = Fintype.card α := by omega
    have heq' : (Finset.univ.image f).card = (Finset.univ : Finset α).card := by
      simpa using heq
    have hinj : Set.InjOn f (Finset.univ : Finset α) := Finset.card_image_iff.mp heq'
    intro a b hab
    exact hinj (Finset.mem_univ a) (Finset.mem_univ b) hab
  · intro hinj
    have hcard : (Finset.univ.image f).card = Fintype.card α := by
      simpa using Finset.card_image_of_injective (s := (Finset.univ : Finset α)) hinj
    omega

-- ============ K₀ 群：Quotient holeRel ≅ ℤ ============

/-
  【Grothendieck 群的实算：洞荷群 ≅ ℤ】

  K₀ 的标准结果：(ℕ × ℕ, +) 形式加逆元后得到 ℤ。
  这里把它算出来：Quotient holeRel ≃ ℤ，映射就是"洞 − 浪费"。

  于是"洞的荷"有了完全精确的身份：它是整数 |β| − |α|，
  由空间几何决定，与枚举无关（holeCharge_int）。
-/

-- 形式差就是整数减法：holeRel p q ⟺ p 的"差" = q 的"差"。
theorem holeRel_iff_sub (p q : ℕ × ℕ) :
    holeRel p q ↔ (p.1 : ℤ) - (p.2 : ℤ) = (q.1 : ℤ) - (q.2 : ℤ) := by
  unfold holeRel
  constructor <;> intro h <;> omega

-- 任意整数都能写成 toNat 与 (-·).toNat 之差（K₀ 的"代表元"）。
theorem int_toNat_sub_neg (z : ℤ) : (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by
  by_cases h : 0 ≤ z
  · rw [Int.toNat_of_nonneg h]
    have h' : (-z).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [h']
    simp
  · have h' : z.toNat = 0 := Int.toNat_of_nonpos (le_of_lt (not_le.mp h))
    rw [h']
    have h2 : 0 ≤ -z := by omega
    rw [Int.toNat_of_nonneg h2]
    simp

-- 洞的 K₀ 群（形式差商）。
abbrev HoleGroup : Type := Quot holeRel

-- 到 ℤ 的"差"映射。
def holeGroupToInt : HoleGroup → ℤ :=
  Quot.lift (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))
    (fun p q h => (holeRel_iff_sub p q).mp h)

-- 从 ℤ 回来（z 与 −z 的 toNat 之差）。
def intToHoleGroup (z : ℤ) : HoleGroup :=
  Quot.mk holeRel (z.toNat, (-z).toNat)

theorem holeGroupToInt_intToHoleGroup (z : ℤ) :
    holeGroupToInt (intToHoleGroup z) = z := by
  show (z.toNat : ℤ) - ((-z).toNat : ℤ) = z
  exact int_toNat_sub_neg z

theorem intToHoleGroup_holeGroupToInt (q : HoleGroup) :
    intToHoleGroup (holeGroupToInt q) = q := by
  induction q using Quot.ind with
  | _ p =>
      apply Quot.sound
      exact (holeRel_iff_sub _ _).mpr (int_toNat_sub_neg ((p.1 : ℤ) - (p.2 : ℤ)))

-- K₀ 群 ≅ ℤ（Grothendieck 群的实际计算）。
def holeGroupEquivInt : HoleGroup ≃ ℤ where
  toFun := holeGroupToInt
  invFun := intToHoleGroup
  left_inv := intToHoleGroup_holeGroupToInt
  right_inv := holeGroupToInt_intToHoleGroup

-- 【两种对位】加法对位（洞荷 K₀ ≅ ℤ）与乘法对位（比值 ≅ ℚ）是同一个
-- 交叉模式的两种实例；整数通过"分母为 1 的整份对位"嵌入 ℚ。
theorem cross_pattern_duality :
    Nonempty (HoleGroup ≃ ℤ) ∧ Nonempty (Alignment ≃ ℚ) ∧
      Function.Injective intToAlignment :=
  ⟨⟨holeGroupEquivInt⟩, ⟨alignmentEquivRat⟩, intToAlignment_injective⟩

-- 洞荷在 K₀ 群里的像 = 整数 |β| − |α|，与枚举无关。
theorem holeCharge_int {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hαβ : Fintype.card α ≤ Fintype.card β) :
    holeGroupToInt (Quot.mk holeRel (holeCharge f))
      = (Fintype.card β : ℤ) - (Fintype.card α : ℤ) := by
  show ((holeCharge f).1 : ℤ) - ((holeCharge f).2 : ℤ)
      = (Fintype.card β : ℤ) - (Fintype.card α : ℤ)
  have h := holeCount_index f hαβ
  unfold holeCharge
  omega

-- ============ K₀ 的函子性：洞荷在不相交并下可加 ============

/-
  【K₀ 是函子：洞荷对"不相交并"可加】

  K₀ 的标准性质是可加性（函子性）。这里把它做出来：
  给定 f : α → β 和 g : α' → β'，它们的"并" f ⊔ g : α ⊕ α' → β ⊕ β'
  满足      洞(f ⊔ g) = 洞(f) + 洞(g)，浪费同理。

  于是 holeCharge 是幺半群同态，K₀ 群 ≅ ℤ 的映射也是加法同态——
  "洞的荷"真正成为一个可加的群元素，而不只是单个不变量。
-/

-- 不相交并上的映射。
def sumMap {α β α' β' : Type*} (f : α → β) (g : α' → β') : α ⊕ α' → β ⊕ β'
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr a' => Sum.inr (g a')

-- 像的基数可加（f 的像与 g 的像在 β ⊕ β' 里不相交）。
theorem card_image_sumMap {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq β] [DecidableEq β']
    (f : α → β) (g : α' → β') :
    (Finset.univ.image (sumMap f g)).card
      = (Finset.univ.image f).card + (Finset.univ.image g).card := by
  -- 左像 = inl 部分 ∪ inr 部分
  have himg : Finset.univ.image (sumMap f g)
      = Finset.univ.image (fun a : α => (Sum.inl (f a) : β ⊕ β'))
        ∪ Finset.univ.image (fun a' : α' => (Sum.inr (g a') : β ⊕ β')) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s, hs⟩
      cases s with
      | inl a => exact Or.inl ⟨a, hs⟩
      | inr a' => exact Or.inr ⟨a', hs⟩
    · rintro (⟨a, rfl⟩ | ⟨a', rfl⟩)
      · exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr a', rfl⟩
  -- 两部分不相交
  have hdisj : Disjoint (Finset.univ.image (fun a : α => (Sum.inl (f a) : β ⊕ β')))
      (Finset.univ.image (fun a' : α' => (Sum.inr (g a') : β ⊕ β'))) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    have h : (Sum.inl (f a) : β ⊕ β') = Sum.inr (g a') := ha.trans ha'.symm
    cases h
  -- 两部分的基数 = |im f| 与 |im g|
  have hcA : (Finset.univ.image (fun a : α => (Sum.inl (f a) : β ⊕ β'))).card
      = (Finset.univ.image f).card := by
    have h1 : Finset.univ.image (fun a : α => (Sum.inl (f a) : β ⊕ β'))
        = (Finset.univ.image f).image (fun b : β => (Sum.inl b : β ⊕ β')) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨f a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨b, ⟨a, rfl⟩, rfl⟩; exact ⟨a, rfl⟩
    rw [h1]
    exact Finset.card_image_of_injective _ Sum.inl_injective
  have hcB : (Finset.univ.image (fun a' : α' => (Sum.inr (g a') : β ⊕ β'))).card
      = (Finset.univ.image g).card := by
    have h1 : Finset.univ.image (fun a' : α' => (Sum.inr (g a') : β ⊕ β'))
        = (Finset.univ.image g).image (fun b' : β' => (Sum.inr b' : β ⊕ β')) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a', rfl⟩; exact ⟨g a', ⟨a', rfl⟩, rfl⟩
      · rintro ⟨b', ⟨a', rfl⟩, rfl⟩; exact ⟨a', rfl⟩
    rw [h1]
    exact Finset.card_image_of_injective _ Sum.inr_injective
  rw [himg, Finset.card_union_of_disjoint hdisj, hcA, hcB]

-- 洞数可加。
theorem holeCount_sumMap {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq β] [DecidableEq β']
    (f : α → β) (g : α' → β') :
    holeCount (sumMap f g) = holeCount f + holeCount g := by
  have h1 : holeCount (sumMap f g)
      = Fintype.card (β ⊕ β') - (Finset.univ.image (sumMap f g)).card := by
    unfold holeCount holeSet
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have h2 : holeCount f = Fintype.card β - (Finset.univ.image f).card := by
    unfold holeCount holeSet
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have h3 : holeCount g = Fintype.card β' - (Finset.univ.image g).card := by
    unfold holeCount holeSet
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  rw [h1, h2, h3, card_image_sumMap f g, Fintype.card_sum]
  have him1 : (Finset.univ.image f).card ≤ Fintype.card β := by
    simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ.image f))
  have him2 : (Finset.univ.image g).card ≤ Fintype.card β' := by
    simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ.image g))
  omega

-- 浪费可加。
theorem redundantHoles_sumMap {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq β] [DecidableEq β']
    (f : α → β) (g : α' → β') :
    redundantHoles (sumMap f g) = redundantHoles f + redundantHoles g := by
  unfold redundantHoles
  rw [card_image_sumMap f g, Fintype.card_sum]
  have him1 : (Finset.univ.image f).card ≤ Fintype.card α := by
    simpa using Finset.card_image_le (f := f) (s := (Finset.univ : Finset α))
  have him2 : (Finset.univ.image g).card ≤ Fintype.card α' := by
    simpa using Finset.card_image_le (f := g) (s := (Finset.univ : Finset α'))
  omega

-- 【K₀ 函子性】洞荷可加：holeCharge 是幺半群同态。
theorem holeCharge_sumMap {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq β] [DecidableEq β']
    (f : α → β) (g : α' → β') :
    holeCharge (sumMap f g) = holeCharge f + holeCharge g := by
  unfold holeCharge
  rw [holeCount_sumMap f g, redundantHoles_sumMap f g]
  rfl

-- K₀ 群上的加法同态：洞荷映射保持加法。
theorem holeCharge_int_add {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq β] [DecidableEq β']
    (f : α → β) (g : α' → β') :
    holeGroupToInt (Quot.mk holeRel (holeCharge (sumMap f g)))
      = holeGroupToInt (Quot.mk holeRel (holeCharge f))
        + holeGroupToInt (Quot.mk holeRel (holeCharge g)) := by
  rw [holeCharge_sumMap f g]
  show (((holeCharge f).1 + (holeCharge g).1 : ℕ) : ℤ) - (((holeCharge f).2 + (holeCharge g).2 : ℕ) : ℤ)
      = (((holeCharge f).1 : ℤ) - ((holeCharge f).2 : ℤ))
        + (((holeCharge g).1 : ℤ) - ((holeCharge g).2 : ℤ))
  push_cast
  ring

-- ============ 「层」与「洞」的对偶：封闭 vs 敞开 ============

/-
  【层 = 封闭（凝结满射，无余核）；自指 = 敞开（必有洞）】

  这是差异论两种数学的分界线：

    · 凝结（层）：Quotient.mk 永远是满射。像 = 整个目标空间，
      余核为空 ⟹ 洞数 = 0。层是**封闭**的——一切都被凝结进来。
    · 自指：任何 f : α → resolveSpace α 永远不满射（康托尔）。
      余核非空 ⟹ 洞数 > 0。自指是**敞开**的——总有什么够不着。

  所以"层"与"洞"不是两个概念，是有限性的两个方向：
  一个把一切收拢（凝结），一个永远留出开口（对角线）。
  这就是为什么"层"能做成 sheaf（粘合完备），而"自指"只能做成熵（必然有漏）。
-/

-- 满射 ⟹ 余核为空 ⟹ 洞数为零（凝结的洞数恒为 0）。
theorem holeCount_eq_zero_of_surjective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Surjective f) : holeCount f = 0 := by
  unfold holeCount holeSet
  have himage : (Finset.univ.image f) = (Finset.univ : Finset β) := by
    ext b
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, _, _⟩
      exact Finset.mem_univ b
    · intro _
      obtain ⟨a, ha⟩ := hf b
      exact ⟨a, Finset.mem_univ a, ha⟩
  rw [himage]
  simp

-- 商映射（凝结）永远满射：层的余核恒为空。
theorem quotient_mk_surjective {α : Type*} (s : Setoid α) :
    Function.Surjective (Quotient.mk s) := fun q => Quotient.exists_rep q

-- 【对偶定理】层封闭、自指敞开：凝结的洞数恒为 0，自指的洞数恒为正。
theorem layer_closed_self_open :
    -- 层：凝结满射 ⟹ 无洞
    (∀ {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β),
        Function.Surjective f → holeCount f = 0) ∧
    -- 自指：任何枚举都有洞
    (∀ {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α), 0 < holeCount f) :=
  ⟨fun f hf => holeCount_eq_zero_of_surjective f hf,
   fun f => entropy_positive_via_counting f⟩

-- ============ 洞的五张脸（枢纽定理） ============

/-
  【洞的五张脸：一个对象，五种数学】

  ① 对角线（自指层）：diag f 永远够不着——洞 = 不可达。
  ② 计数（组合层）：熵 = 洞的数量 = |β| − |像|——洞 = 余核。
  ③ 指标（代数层）：熵 − 冗余 = 2^n − n——洞的净荷由几何决定，与枚举无关。
  ④ 必然（有限性）：熵恒正——只要 n < 2^n，洞就存在。
  ⑤ 再生（结构层）：堵一个必生一个——洞是有限性的结构性开口。

  五张脸分属四个数学层（对角线 / 计数 / 代数-指标 / 结构），却指向同一个对象。
  "洞是枢纽"说的就是这件事：它不是某一层里的一个概念，
  而是**唯一一个横跨全部层的对象**——所以它能把四层数学焊在一起。
-/
theorem hole_five_faces {α : Type*} [Fintype α] [DecidableEq α] (f : α → resolveSpace α) :
    -- ① 对角洞够不着
    (∀ a : α, diag f ≠ f a) ∧
    -- ② 熵 = 洞的数量（余核）
    (entropy f = (blindSet f).card) ∧
    -- ③ 指标：洞的净荷由几何决定（不变量）
    (entropy f + Fintype.card α
      = (Fintype.card α - (Finset.univ.image f).card) + 2 ^ Fintype.card α) ∧
    -- ④ 洞必然存在
    (0 < entropy f) ∧
    -- ⑤ 堵一个必生一个
    (∀ f' : α → resolveSpace α, (∃ a₀ : α, f' a₀ = diag f) → diag f' ≠ diag f) :=
  ⟨fun a => diag_ne_apply f a, entropy_eq_blindSet_card f, entropy_index f,
   entropy_positive_via_diag f, fun f' h => hole_reborn f f' h⟩

-- ============ Lawvere 不动点定理：可逆 = 自指的不动点（一般形式） ============

/-
  【Lawvere 不动点：把"可逆 = 不动点"从 reflect 推广到任意自指】

  Lawvere：若 A 能满射枚举所有 A → B（自指枚举），则每个 f : B → B 都有不动点。
  —— 自指满射 ⟹ 每个自映射可逆（有回到自己的点）。

  康托尔对偶：Bool 的否定 not 没有不动点（¬True = False, ¬False = True 都不等于自己），
  所以不存在满射 A → (A → Bool)——自指必有盲区（够不着的分辨），这就是"洞"。

  于是"可逆 = 自指有不动点"有了完全一般的形式，不再局限于 reflect 这一个算子。
  而"洞"（康托尔对角线）是"not 无不动点"的推论：自指永远够不着对角分辨。
  全程构造性：满射的 witness 直接给出不动点，无需选择公理 / 排中律。
-/

-- Lawvere：自指满射 ⟹ 每个 f : B → B 有不动点（可逆点）。
theorem lawvere_fixed_point {A B : Type*} (e : A → (A → B)) (hsurj : Function.Surjective e)
    (f : B → B) : ∃ b : B, f b = b := by
  let g : A → B := fun a => f (e a a)
  obtain ⟨a0, ha0⟩ := hsurj g
  refine ⟨e a0 a0, ?_⟩
  have h : g a0 = e a0 a0 := by
    rw [← ha0]
  calc
    f (e a0 a0) = g a0 := by simp [g]
    _ = e a0 a0 := h

-- Bool 的否定无不动点（¬True = False ≠ True，¬False = True ≠ False）。
theorem not_no_fixed_point : ¬ ∃ b : Bool, (!b) = b := by
  intro h
  obtain ⟨b, hb⟩ := h
  cases b <;> norm_num at hb

-- 康托尔定理（Lawvere 的对偶）：不存在满射 A → (A → Bool)——自指必有盲区（洞）。
theorem cantor_no_surj (A : Type*) : ¬ ∃ e : A → (A → Bool), Function.Surjective e := by
  intro h
  obtain ⟨e, hsurj⟩ := h
  have hfp : ∃ b : Bool, (!b) = b := lawvere_fixed_point e hsurj Bool.not
  exact not_no_fixed_point hfp

-- ============ 群体熵增 ⟷ 雪球：无统一自我 = 无统一不动点 ============

/-
  【群体熵增 ⟷ 雪球：无统一自我 ⟹ 无统一雪球稳定点】

  雪球定理的稳定（s/r = n）就是"单自我自指的不动点"（reflect_fixed_point_iff_stable）。
  单主体用 reflect 把 s/r 调到自己的层级 n，在不动点处停住损耗（对抗熵增）。

  群体 = 多个自我，各有各的层级 n，没有统一的 s/r = n（没有统一的自我），
  故没有统一的不动点——熵增单调不可逆（时间之箭）。

  反例：两个主体对 (0,0)~(0,0) 的雪球比是 0/2 = 0，而 (1,0)~(0,0) 的是 1/2，
  雪球比不同 → 群体无统一稳定点。这正是"群体无法自指"的雪球版。
-/

-- 群体的雪球比：两个主体的差异簇数 / 公共维度（ℚ）。
def pairSnowballRatio {m n : ℕ} (x : StateQuant m) (y : StateQuant n) : ℚ :=
  (s_rel x y : ℚ) / (r_rel x y : ℚ)

-- 群体无统一雪球稳定点：存在两个主体对，雪球比不同（0 ≠ 1/2）。
theorem group_no_unified_snowball :
    ∃ m n : ℕ, ∃ x1 : StateQuant m, ∃ y1 : StateQuant n,
      ∃ x2 : StateQuant m, ∃ y2 : StateQuant n,
        pairSnowballRatio x1 y1 ≠ pairSnowballRatio x2 y2 := by
  let x1 : StateQuant 2 := { val := fun _ => 0, phase := .neutral }
  let y1 : StateQuant 2 := { val := fun _ => 0, phase := .neutral }
  let x2 : StateQuant 2 := { val := fun i => if i.val = 0 then 1 else 0, phase := .neutral }
  let y2 : StateQuant 2 := { val := fun _ => 0, phase := .neutral }
  refine ⟨2, 2, x1, y1, x2, y2, ?_⟩
  unfold pairSnowballRatio
  have hs1 : s_rel x1 y1 = 0 := by native_decide
  have hs2 : s_rel x2 y2 = 1 := by native_decide
  rw [hs1, hs2]
  norm_num [r_rel]

-- ============ 表演：从差异论公理推出代数结构（环/域） ============

/-
  【从差异论公理到代数环/域：一个诚实的表演】

  代数环（ring）＝一个集合 + 两个运算 ⊕、⊗，满足：
    (1) ⊕ 结合、交换、有幺元（加法交换群）；
    (2) ⊗ 结合、有幺元；
    (3) ⊗ 对 ⊕ 分配。
  代数域（field）＝环 + 每个非零元有乘法逆。

  差异论公理直接给出两个候选运算：
    · 差异合成 ⊕_D（composeD）：把两个差异合成一个差异；
    · ℚ 的算术（加法 +、乘法 ×）：差异论全程坐在 ℚ 上。

  结果出人意料地干净：
    (A) ⊕_D 交换（composeD_comm），但不结合（composeD_not_assoc，下面反例）。
        所以 ⊕_D 不是环——它只到"交换 magme"。这精确呼应原文"差异合成不是加法"：
        加法（阿贝尔群）是交换 + 结合，差异合成交换却不结合，因为"爆炸区取和"破坏了结合。
    (B) 但差异论全程用 ℚ，而 ℚ 是域（Field）。所以"代数域"不是从 ⊕_D 推出来的，
        而是从"ℚ 根"直接长出来的——差异论坐在一个代数域上。

  结论一句话：差异论推不出"差异合成的环"（不结合），但差异论坐在"域（ℚ）"上。
-/

-- (A) ⊕_D 不结合：反例 τ_c = 0, a = -1, b = -2, c = 10。
--     (a ⊕ b) ⊕ c = (max -1 -2) ⊕ 10 = -1 ⊕ 10 = 9
--     a ⊕ (b ⊕ c) = -1 ⊕ (-2 ⊕ 10) = -1 ⊕ 8 = 7
--     9 ≠ 7。
theorem composeD_not_assoc :
    ∃ τ_c a b c : ℚ,
      composeD τ_c (composeD τ_c a b) c ≠ composeD τ_c a (composeD τ_c b c) := by
  refine ⟨0, -1, -2, 10, ?_⟩
  norm_num [composeD]

-- (B) 差异论坐在域上：ℚ 是代数域（Field），非零元有乘法逆（域的判定特征）。
example : Field ℚ := inferInstance

-- ============ 三生万物：resolveSpace 自动长出 classCount 的分辨空间 ============

/-
  【自我繁殖的第一次落地：类型分辨空间】

  classCount δ = 色环上连通分量的个数（类型数）。
  resolveSpace（一分为二）套在"类型"（Quotient）上，自动长出
  2^classCount 个分辨结果——这不是手搓的第 42 个模块，
  是 resolve_card 套在 Quotient 上的自动结果。

  一分为二（resolveSpace）+ 有限闭包（Quotient.fintype）
    = 类型分辨空间（2^classCount 的布尔代数）。

  这才是"自我繁殖"：一个 resolveSpace，套在色环的类型上，
  结构自己长出来，不用手写任何新定理。
-/

-- 类型分辨空间 = 2^classCount：这不过是 resolve_card 套在 Fin (classCount …) 上，
-- 不另立定理（"自己长出来"的第一条纪律：能由 resolve_card 得的，不再手写一遍）。

-- 类型分辨 ≤ 位置分辨：2^classCount ≤ 2^k（类数 ≤ 元素数）。
theorem type_resolution_le_position {k : ℕ} (δ : ℕ) :
    Fintype.card (resolveSpace (Fin (classCount (k := k) δ))) ≤ Fintype.card (resolveSpace (Fin k)) := by
  simp
  exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (classCount_le_k δ)

end Ego

-- ============ 构造性根基：计数层的 Classical 是可消除的 ============

/-
  【从唯一根导出的机械化审计（#print axioms）】

  审计结果：
    · 核心概念（洞、自指、不动点）零 Classical：
        lawvere_fixed_point / diagonal_hole 只依赖 [propext]（命题外延，无害）。
    · 计数层（Finset.card 的卡类比较）被 Mathlib 的 Multiset 序理论
      （le_iff_subset、dedup_le，基于 Subperm）"经典化"了，依赖 Classical.choice。

  但计数层的 Classical 是可消除的——下面 card_filter_le_constructive 经 Multiset
  直接证，零 Classical（[propext, Quot.sound]）。这说明"从根导出"在概念上成立，
  Classical 只是 Mathlib 的证明风格；彻底消除需构造化 Multiset 的 Subperm（大工程）。
-/

-- 构造性卡类（代表）：filter 的势 ≤ 原势，零 Classical。
theorem card_filter_le_constructive {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card ≤ s.card := by
  change Multiset.card (s.filter p).val ≤ Multiset.card s.val
  simpa using (Multiset.card_le_card (Multiset.filter_le p s.val))

-- ============ 同构搬运：resolveSpace 本来就是布尔代数 ============

/-
  【准确说：resolveSpace 从定义起就是布尔代数，不靠搬运】

  resolveSpace α = α → Bool，而 Bool 是 BooleanAlgebra，函数类型（Pi）的点式
  布尔代数在 Mathlib 里自动存在——所以 BooleanAlgebra (resolveSpace α) 从写下
  abbrev 那一刻就生效，不需要搬运、不需要 Fintype / DecidableEq。

  resolveEquivFinset（分辨 ≃ 集合）是"桥"：它把分辨的布尔格和集合的布尔格
  对应起来。白拿定理用 Pi 自动的点式实例即可，无需额外声明 instance。
-/

-- 白拿展示：resolveSpace 的布尔格定理（吸收律、De Morgan）自动成立，一行不写。
-- （simp 用的是 Pi 的点式布尔代数，从 abbrev 定义起就生效。）
example {α : Type*} (f g : Ego.resolveSpace α) : f ⊓ (f ⊔ g) = f := by simp
example {α : Type*} (f g : Ego.resolveSpace α) : (f ⊔ g)ᶜ = fᶜ ⊓ gᶜ := by simp

-- ============ 同构搬运推广（克制版）：StateQuant.val 是向量空间 ============

/-
  【推广：状态 val 接上向量空间】

  StateQuant.val : Fin n → ℚ 是向量空间元素（AddCommGroup 自动），
  白拿线性组合：加法、标量乘法、0 元、负元。这是"态叠加"的离散版——
  状态的 val 可以线性组合，像量子态叠加一样。

  不喧宾夺主：只声明身份、白拿结构；差异论独有的大定理（洞/熵/对位）不在这里。
-/

-- val 是向量空间元素（AddCommGroup 自动给出）。
example {n : ℕ} : AddCommGroup (Fin n → ℚ) := inferInstance

-- 白拿：val 的线性组合（0 元、标量分配 = 态叠加）。
example {n : ℕ} (x : StateQuant n) : (0 : Fin n → ℚ) + x.val = x.val := by simp
example {n : ℕ} (x y : StateQuant n) (c : ℚ) :
    c • (x.val + y.val) = c • x.val + c • y.val := by
  rw [smul_add]

-- ============ 证明即排序：验证 = 逐步骤检查（Decidable） ============

/-
  【证明即排序（P vs NP 直觉的落地半）】

  证明 = 一条推理步骤序列（从公理走到结论），
  验证证明 = 检查序列每步是否合法（可判定）。

  这和"排序"同构：排序 = 找排列使相邻有序，验证排序 = 检查相邻 ≤。
  "找到"（证明/排序）是 NP 侧，"验证"（检查）是 P 侧（可判定）。

  这里落地"验证"侧：验证证明 = 逐步骤检查，全程 Decidable（构造性）。
  呼应差异论全程用 Decidable——"验证"是构造性的，差异论一直站在 P 侧。
-/

-- 一步推理规则（Bool，可判定）：b 由 a 经"规则"得到。
def stepRel (a b : ℕ) : Bool := b == a + 1

-- 证明 = 序列 [a₀, ..., aₙ]，相邻每步满足 stepRel（Bool 判定）。
def isProof : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => stepRel a b && isProof (b :: rest)

-- 验证证明可判定：Bool 自动 Decidable，逐步骤检查，构造性（无 Classical）。
example (seq : List ℕ) : Decidable (isProof seq = true) := inferInstance

-- ============ 找到侧：对位保证存在性（NP 侧的差异论答案） ============

/-
  【找到存在性：不靠暴力搜索，靠对位（关系）】

  找到侧（NP）= 构造存在性（∃ x, P x）。差异论的答案是：
  不是暴力枚举序列，而是"对位"——类型之间互补（洞被有填），
  通过关系（对位）定位目标。

  你活在世界上，总有关系（对位），所以总能找到你：
  任何"有"（y）都有一个"洞"（x = 全 0）来对位（填洞），
  存在性由构造保证（零 Classical）。
-/

-- 对位：x 和 y 互补（x 的洞（0）处 y 有（非 0））。
def Aligned {n : ℕ} (x y : StateQuant n) : Prop :=
  ∀ i : Fin n, x.val i = 0 → y.val i ≠ 0

-- 对位保证存在：任何 y 都有对位者 x（x 的洞恰好填 y 的有）。
-- "你活在世界上，总有关系（对位），总能找到你"的形式化。
theorem alignment_guarantees_existence {n : ℕ} (y : StateQuant n) :
    ∃ x : StateQuant n, Aligned x y := by
  let x : StateQuant n := { val := fun i => if y.val i = 0 then 1 else 0, phase := .neutral }
  refine ⟨x, ?_⟩
  intro i hx
  by_contra h
  have hx1 : x.val i = 1 := by simp [x, h]
  rw [hx1] at hx
  norm_num at hx

-- ============ 两种洞的对偶：可填的洞 vs 不可填的洞 ============

/-
  【两种洞的对偶：状态空间的洞可填，分辨空间的洞不可填】

  "对位填的洞 ≠ 康托尔洞"——它们不在同一个空间：

    · 状态空间的洞（维度缝隙 [m, max m n)）：
      由"有"（y 的非零分量）来填，对位保证总能找到填充者。
      所以：∀ y, ∃ x, Aligned x y ——**可填**。

    · 分辨空间的洞（康托尔对角线）：
      任何枚举 f 都漏 diag f，且堵一个必生一个。
      所以：∀ f, 0 < entropy f ——**不可填**。

  这就是"洞作为枢纽"的第二个硬事实：
  同一个词"洞"，在两个空间里扮演两种不同角色——
  在状态空间是可交易的缺口（对位/交易），在分辨空间是不可磨灭的开口（熵/时间之箭）。
-/
theorem two_kinds_of_holes :
    -- 状态空间的洞：总可被对位填满
    (∀ {n : ℕ} (y : StateQuant n), ∃ x : StateQuant n, Aligned x y) ∧
    -- 分辨空间的洞：任何枚举都填不满
    (∀ {α : Type*} [Fintype α] [DecidableEq α] (f : α → Ego.resolveSpace α), 0 < Ego.entropy f) :=
  ⟨fun y => alignment_guarantees_existence y, fun f => Ego.entropy_positive_via_diag f⟩

-- ============ 同构降复杂度：调集不同领域的定理 ============

/-
  【降复杂度 = 同构搬运到"有现成武器"的领域】

  元理论的降复杂度：难问题（暴力枚举）通过"同构"搬到"有现成高效定理"的
  领域，用那个领域的定理一行验证。

  例：布尔恒等式 f ⊓ (f ⊔ g) = f。
    暴力侧：枚举 f、g 的 2^|α| 种赋值——O(2^n)。
    同构侧：resolveSpace 是 BooleanAlgebra，吸收律现成，by simp——O(1)。

  这就是"调集不同领域的定理进行同构运行验证"：同构把"枚举"变"一行定理"。
-/

-- 同构降复杂度：吸收律 by simp 一行，不枚举 2^|α| 种赋值
-- （前文"白拿展示"已列过 f ⊓ (f ⊔ g) = f，此处不重抄）。

-- 同构运行验证：同一恒等式在"集合"领域（∩）也成立（resolveSpace ≃ Finset）。
example {α : Type*} [DecidableEq α] (s t : Finset α) : s ∩ (s ∪ t) = s := by simp

-- ============ 单个差异对象 = 消解的核（微积分的有限版） ============

/-
  【单个差异对象：消解后的不可磨灭核】

  微积分：微分/积分互逆，用"无穷逼近"（极限）抓住无穷小/无穷大。
  差异论：凝结/消解互逆（coarsen_condense_eq），用"消解"（有限构造）抓住
  "不可磨灭的核"——强制消解后剩下的、消解不掉的差异对象。

  消解（coarsen）把 x 投影到 n 维：[0, n) 保留（核，不可磨灭），
  [n, m) 消掉（变洞 = 0）。这个"洞"就是"得以交易的部分"（对位填洞）。
  核是"单个差异对象"，洞是"可交易的部分"——这就是"三体运动无不动点"的
  差异论答案：不是找不动点，是消解出核。
-/

-- 消解的核：coarsen 保留 [0, n)（核），[n, m) 变洞（可交易）。
theorem coarsen_residue {m n : ℕ} (h : n ≤ m) (x : StateQuant m) (i : Fin n) :
    (Ego.coarsen h x).val i = x.val ⟨i.val, lt_of_lt_of_le i.isLt h⟩ := by
  unfold Ego.coarsen
  rfl

-- 消解的洞：condense（凝结）补的 0（[n, m) 的洞）等待"有"来填（对位/交易）。
theorem condense_hole {m n : ℕ} (x : StateQuant n) (i : Fin m) (hi : n ≤ i.val) :
    (Ego.condense x).val i = 0 := by
  unfold Ego.condense
  simp [not_lt_of_ge hi]

-- ============ 群体熵增完整：消解不可逆，洞单调不减 ============

/-
  【群体熵增完整：消解 → 洞（熵）单调不减】

  群体（多个主体）无统一不动点（group_no_unified_snowball），所以只能熵增。
  这里补上"熵增单调"：消解（coarsen）不可逆地丢失差异（D6），
  再凝结（condense）补 0 = 洞，洞是"不可磨灭的损耗"（熵）。

  核（[0, n)）守恒（coarsen_residue），洞（[n, m) 的 0）单调不减（熵增）。
  这就是"时间之箭不可逆"：消解丢掉的差异，再也回不来（洞是损耗）。
-/

-- 群体熵增：消解再凝结（condense ∘ coarsen）丢失 [n, m) 的差异（变洞）。
-- 洞 = 不可逆的损耗（熵增）——消解丢掉的差异，凝结只补 0，回不到原值。
theorem coarsen_then_condense_hole {m n : ℕ} (h : n ≤ m) (x : StateQuant m) (i : Fin m) (hi : n ≤ i.val) :
    (Ego.condense (Ego.coarsen h x)).val i = 0 := by
  unfold Ego.condense Ego.coarsen
  simp [not_lt_of_ge hi]

-- 熵增单调：消解后，洞（[n, m) 的 0）不会减少——
-- 一旦消解成洞，凝结只能补 0，回不到原值（不可逆 = 时间之箭）。
theorem hole_monotone {m n : ℕ} (h : n ≤ m) (x : StateQuant m) (i : Fin m) (hi : n ≤ i.val) :
    (Ego.condense (Ego.coarsen h x)).val i ≠ x.val i ∨ x.val i = 0 := by
  by_cases hx : x.val i = 0
  · right; exact hx
  · left
    rw [coarsen_then_condense_hole h x i hi]
    intro h'
    exact hx h'.symm

-- ============ τ_c 归约：相变阈值从有限性逼出 ============

/-
  【τ_c 归约：像 δ 一样，从"有限 ⇒ 台阶"逼出】

  δ 的归约（已做）：δ 的有效取值 = 差异绝对值集合（absDiffVals），有限。
  τ_c 的归约（这里）：τ_c 的有效取值 = ⊕_D 的输入（a、b），有限。

  ⊕_D（composeD）的行为只在 τ_c 跨越 max a b 时改变：
    · τ_c > max a b（即 a, b < τ_c）：线性 max；
    · τ_c ≤ max a b：爆炸 +。
  所以 τ_c 的台阶恰在 max a b 处——τ_c 的有效取值 = {a, b}（有限），
  由"有限 ⇒ 台阶"逼出，不依赖任何外部给定的连续阈值。
-/

-- τ_c 台阶（线性侧）：τ_c > max a b 时，⊕_D = max（线性）。
theorem composeD_step_linear {τ_c a b : ℚ} (h : max a b < τ_c) :
    Ego.composeD τ_c a b = max a b := by
  unfold Ego.composeD
  have ha : a < τ_c := lt_of_le_of_lt (le_max_left a b) h
  have hb : b < τ_c := lt_of_le_of_lt (le_max_right a b) h
  simp [ha, hb]

-- τ_c 台阶（爆炸侧）：τ_c ≤ max a b 时，⊕_D = +（爆炸）。
theorem composeD_step_explosive {τ_c a b : ℚ} (h : τ_c ≤ max a b) :
    Ego.composeD τ_c a b = a + b := by
  unfold Ego.composeD
  have hnot : ¬ (a < τ_c ∧ b < τ_c) := by
    intro h'
    exact not_lt_of_ge h (max_lt h'.1 h'.2)
  simp [hnot]

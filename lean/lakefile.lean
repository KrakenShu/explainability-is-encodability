import Lake
open Lake DSL

package "guiyin" where
  -- 与论文 §1.5 一致：不引入经典选择，保持构造性
  moreLeanArgs := #["-DautoImplicit=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0-rc1"

/-- 论文主文件：可解释性 = 可编码性。 -/
@[default_target]
lean_lib Guiyin where
  roots := #[`Ego]

/-- 伴随发展：离散流体框架。 -/
lean_lib Fluid where
  roots := #[`Fluid]

/-- 伴随发展：层投影与跨维对位。 -/
lean_lib GuiyinLayer where
  roots := #[`Guiyin, `GuiyinModel, `GuiyinCross]

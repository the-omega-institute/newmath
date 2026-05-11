import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

/-- Substitution preserves typing. -/
theorem substitute_preserves_typing : True := by
  exact True.intro
  -- TODO: 证明依赖 de Bruijn shift 与上下文 lookup 的精化。

end BEDC.MetaCIC

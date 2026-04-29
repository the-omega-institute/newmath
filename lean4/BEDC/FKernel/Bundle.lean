import BEDC.FKernel.Ask

/-! Probe bundles are internally generated records, not exposed host lists. -/
namespace BEDC.FKernel.Bundle

open BEDC.FKernel.Ask


axiom ProbeBundle : Type
axiom Bnil : ProbeBundle
axiom Bcons : ProbeName → ProbeBundle → ProbeBundle
axiom InBundle : ProbeName → ProbeBundle → Prop

end BEDC.FKernel.Bundle

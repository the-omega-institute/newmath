import BEDC.FKernel.Mark
import BEDC.FKernel.Hist

/-! Relational extension of a history by one emitted mark. -/
namespace BEDC.FKernel.Ext

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist

axiom Ext : BHist → BMark → BHist → Prop

theorem ext_deterministic :
    ∀ {h r r' : BHist} {m : BMark}, Ext h m r → Ext h m r' → hsame r r' := by
  sorry

theorem ext_respects_sameness :
    ∀ {h h' r r' : BHist} {m m' : BMark},
      hsame h h' → msame m m' → Ext h m r → Ext h' m' r' → hsame r r' := by
  sorry

end BEDC.FKernel.Ext

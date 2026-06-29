import BEDC.Derived.PreuniformityUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.PreuniformityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PreuniformityCarrier_filter_base_route
    {source entourage base topology transport replay provenance localName baseRead topologyRead :
      BHist}
    (sourceUnary : UnaryHistory source)
    (entourageUnary : UnaryHistory entourage)
    (baseUnary : UnaryHistory base)
    (topologyUnary : UnaryHistory topology)
    (entourageBase : Cont entourage base baseRead)
    (baseTopology : Cont base topology topologyRead) :
    UnaryHistory baseRead ∧ UnaryHistory topologyRead ∧
      Cont entourage base baseRead ∧ Cont base topology topologyRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  have baseReadUnary : UnaryHistory baseRead :=
    unary_cont_closed entourageUnary baseUnary entourageBase
  have topologyReadUnary : UnaryHistory topologyRead :=
    unary_cont_closed baseUnary topologyUnary baseTopology
  have _sourceRow : UnaryHistory source := sourceUnary
  have _transportRow : hsame transport transport := hsame_refl transport
  have _replayRow : hsame replay replay := hsame_refl replay
  have _provenanceRow : hsame provenance provenance := hsame_refl provenance
  have _nameRow : hsame localName localName := hsame_refl localName
  exact ⟨baseReadUnary, topologyReadUnary, entourageBase, baseTopology⟩

end BEDC.Derived.PreuniformityUp

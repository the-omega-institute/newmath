import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FreeMonoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FreeMonoidWordCarrier [AskSetup] [PackageSetup]
    (word route provenance : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory word ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
    Cont word route provenance ∧ PkgSig bundle provenance pkg

theorem FreeMonoidWordCarrier_empty_word_unit [AskSetup] [PackageSetup]
    {word route provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier word route provenance bundle pkg ->
      UnaryHistory BHist.Empty ∧ UnaryHistory word ∧ Cont BHist.Empty word word ∧
        Cont word BHist.Empty word ∧ hsame (append BHist.Empty word) word ∧
          hsame (append word BHist.Empty) word ∧ PkgSig bundle provenance pkg := by
  intro carrier
  rcases carrier with
    ⟨wordUnary, _routeUnary, _provenanceUnary, _wordRouteProvenance, pkgSig⟩
  exact
    ⟨unary_empty, wordUnary, cont_left_unit word, cont_right_unit word,
      append_empty_left word, append_empty_right word, pkgSig⟩

theorem FreeMonoidWordCarrier_concat_associativity [AskSetup] [PackageSetup]
    {u v w uv left vw right route provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier u route provenance bundle pkg ->
      FreeMonoidWordCarrier v route provenance bundle pkg ->
        FreeMonoidWordCarrier w route provenance bundle pkg ->
          Cont u v uv ->
            Cont uv w left ->
              Cont v w vw ->
                Cont u vw right ->
                  PkgSig bundle provenance pkg ->
                    hsame left right := by
  intro _uCarrier _vCarrier _wCarrier uvRow leftRow vwRow rightRow _pkgSig
  unfold Cont at uvRow leftRow vwRow rightRow
  cases uvRow
  cases leftRow
  cases vwRow
  cases rightRow
  exact append_assoc u v w

theorem FreeMonoidWordCarrier_ledger_normal_form [AskSetup] [PackageSetup]
    {word route provenance endpoint : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FreeMonoidWordCarrier word route provenance bundle pkg -> Cont word route endpoint ->
      PkgSig bundle endpoint pkg ->
        UnaryHistory word ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
          UnaryHistory endpoint ∧ Cont word route provenance ∧ Cont word route endpoint ∧
            hsame provenance endpoint ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle endpoint pkg := by
  intro carrier endpointRow endpointSig
  rcases carrier with
    ⟨wordUnary, routeUnary, provenanceUnary, provenanceRow, provenanceSig⟩
  have sameProvenanceEndpoint : hsame provenance endpoint :=
    cont_deterministic provenanceRow endpointRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport provenanceUnary sameProvenanceEndpoint
  exact
    ⟨wordUnary, routeUnary, provenanceUnary, endpointUnary, provenanceRow, endpointRow,
      sameProvenanceEndpoint, provenanceSig, endpointSig⟩

end BEDC.Derived.FreeMonoidUp

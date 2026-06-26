import BEDC.Derived.BooleanalgebraUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BooleanalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BooleanAlgebraMatureExport [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint booleanSource
      latticeRead stoneRead matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg ->
      Cont compl zero endpoint ->
        Cont endpoint one booleanSource ->
          Cont join meet latticeRead ->
            Cont order localName stoneRead ->
              Cont latticeRead stoneRead matureRead ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle matureRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row join ∨ hsame row meet ∨ hsame row compl ∨
                            hsame row zero ∨ hsame row one ∨ hsame row order ∨
                              hsame row latticeRead ∨ hsame row stoneRead ∨
                                hsame row matureRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont join meet latticeRead ∧
                            Cont order localName stoneRead ∧
                              Cont latticeRead stoneRead matureRead ∧
                                PkgSig bundle matureRead pkg)
                        hsame ∧
                      UnaryHistory endpoint ∧ UnaryHistory booleanSource ∧
                        UnaryHistory latticeRead ∧ UnaryHistory stoneRead ∧
                          UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne latticeRoute stoneRoute matureRoute
    _provenancePkg maturePkg
  obtain ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrierRows
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have booleanSourceUnary : UnaryHistory booleanSource :=
    unary_cont_closed endpointUnary oneUnary endpointOne
  have latticeUnary : UnaryHistory latticeRead :=
    unary_cont_closed joinUnary meetUnary latticeRoute
  have stoneUnary : UnaryHistory stoneRead :=
    unary_cont_closed orderUnary localNameUnary stoneRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed latticeUnary stoneUnary matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row latticeRead ∨
                hsame row stoneRead ∨ hsame row matureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont join meet latticeRead ∧ Cont order localName stoneRead ∧
              Cont latticeRead stoneRead matureRead ∧ PkgSig bundle matureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, latticeRoute, stoneRoute, matureRoute, maturePkg⟩
  }
  exact
    ⟨cert, endpointUnary, booleanSourceUnary, latticeUnary, stoneUnary, matureUnary⟩

end BEDC.Derived.BooleanalgebraUp

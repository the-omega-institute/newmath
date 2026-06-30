import BEDC.Derived.BooleanalgebraUp

namespace BEDC.Derived.BooleanalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BooleanAlgebraCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint booleanSource
      stoneRead latticeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont compl zero endpoint →
        Cont endpoint one booleanSource →
          Cont booleanSource localName stoneRead →
            Cont join meet latticeRead →
              Cont latticeRead compl stoneRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle stoneRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row join ∨ hsame row meet ∨ hsame row compl ∨
                            hsame row zero ∨ hsame row one ∨ hsame row order ∨
                              hsame row endpoint ∨ hsame row booleanSource ∨
                                hsame row latticeRead ∨ hsame row stoneRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont compl zero endpoint ∧
                            Cont endpoint one booleanSource ∧
                              Cont booleanSource localName stoneRead ∧
                                Cont join meet latticeRead ∧
                                  Cont latticeRead compl stoneRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle stoneRead pkg)
                        hsame ∧
                      UnaryHistory endpoint ∧ UnaryHistory booleanSource ∧
                        UnaryHistory latticeRead ∧ UnaryHistory stoneRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne booleanSourceLocalName joinMeet latticeStone
    provenancePkg stonePkg
  obtain ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, _orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrierRows
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have booleanSourceUnary : UnaryHistory booleanSource :=
    unary_cont_closed endpointUnary oneUnary endpointOne
  have stoneFromSourceUnary : UnaryHistory stoneRead :=
    unary_cont_closed booleanSourceUnary localNameUnary booleanSourceLocalName
  have latticeUnary : UnaryHistory latticeRead :=
    unary_cont_closed joinUnary meetUnary joinMeet
  have stoneUnary : UnaryHistory stoneRead :=
    unary_cont_closed latticeUnary complUnary latticeStone
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row endpoint ∨
                hsame row booleanSource ∨ hsame row latticeRead ∨ hsame row stoneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compl zero endpoint ∧ Cont endpoint one booleanSource ∧
              Cont booleanSource localName stoneRead ∧ Cont join meet latticeRead ∧
                Cont latticeRead compl stoneRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle stoneRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stoneRead ⟨hsame_refl stoneRead, stoneUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, complZero, endpointOne, booleanSourceLocalName, joinMeet,
          latticeStone, provenancePkg, stonePkg⟩
  }
  exact
    ⟨cert, endpointUnary, booleanSourceUnary, latticeUnary, stoneUnary⟩

end BEDC.Derived.BooleanalgebraUp

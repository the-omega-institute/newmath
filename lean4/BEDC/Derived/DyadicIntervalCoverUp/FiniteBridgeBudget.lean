import BEDC.Derived.DyadicIntervalCoverUp

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverFiniteBridgeBudget [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead coverRead sealRead compactRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont M R coverRead →
            Cont coverRead A sealRead →
              Cont endpointRead sealRead compactRead →
                Cont compactRead N bridgeRead →
                  PkgSig bundle bridgeRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                            hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                              hsame row compactRead ∨ hsame row bridgeRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle bridgeRead pkg ∧
                            PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory compactRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrierRows endpointRoute windowRoute coverRoute sealRoute compactRoute
    bridgeRoute bridgePkg
  obtain ⟨unaryL, unaryU, unaryM, unaryR, _unaryV, unaryW, unaryQ, unaryA, _unaryH,
    _unaryC, provenanceUnary, unaryN, provenancePkg⟩ := carrierRows
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryL unaryU endpointRoute
  have _windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryQ windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed unaryM unaryR coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary unaryA sealRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed endpointUnary sealUnary compactRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed compactUnary unaryN bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row compactRead ∨
                hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle bridgeRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact ⟨source.right, bridgePkg, provenancePkg⟩
  }
  exact ⟨cert, compactUnary, bridgeUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp

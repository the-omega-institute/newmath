import BEDC.Derived.RegularCauchyMidpointUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMidpointNameCertObligations [AskSetup] [PackageSetup]
    {R0 R1 S0 S1 D Q E _H _C P N midpointRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R0 ->
      UnaryHistory R1 ->
        UnaryHistory S0 ->
          UnaryHistory S1 ->
            UnaryHistory D ->
              UnaryHistory Q ->
                UnaryHistory E ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont S0 S1 midpointRead ->
                        Cont midpointRead Q toleranceRead ->
                          Cont toleranceRead E sealRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                PkgSig bundle sealRead pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row R0 ∨ hsame row R1 ∨ hsame row S0 ∨
                                          hsame row S1 ∨ hsame row D ∨ hsame row Q ∨
                                            hsame row E ∨ hsame row sealRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg)
                                      hsame ∧
                                    UnaryHistory midpointRead ∧ UnaryHistory toleranceRead ∧
                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _r0Unary _r1Unary s0Unary s1Unary _dUnary qUnary eUnary _pUnary _nUnary
    midpointRoute toleranceRoute sealRoute provenancePkg namePkg sealPkg
  have midpointUnary : UnaryHistory midpointRead :=
    unary_cont_closed s0Unary s1Unary midpointRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed midpointUnary qUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row R0 ∨ hsame row R1 ∨ hsame row S0 ∨ hsame row S1 ∨ hsame row D ∨
            hsame row Q ∨ hsame row E ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
            PkgSig bundle sealRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, namePkg, sealPkg⟩
  }
  exact ⟨cert, midpointUnary, toleranceUnary, sealUnary⟩

theorem RegularCauchyMidpointRealSealHandoff [AskSetup] [PackageSetup]
    {R0 R1 S0 S1 D Q E _H _C P N leftRead rightRead midpointRead toleranceRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R0 →
      UnaryHistory R1 →
        UnaryHistory S0 →
          UnaryHistory S1 →
            (SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row R0 ∨ hsame row R1 ∨ hsame row S0 ∨ hsame row S1 ∨
                    hsame row D ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                    PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory midpointRead ∧ UnaryHistory toleranceRead ∧
                UnaryHistory sealRead) →
              Cont R0 S0 leftRead →
                Cont R1 S1 rightRead →
                  Cont leftRead rightRead midpointRead →
                    Cont midpointRead Q toleranceRead →
                      Cont toleranceRead E sealRead →
                        PkgSig bundle sealRead pkg →
                          UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                            UnaryHistory midpointRead ∧ UnaryHistory toleranceRead ∧
                              UnaryHistory sealRead ∧ Cont R0 S0 leftRead ∧
                                Cont R1 S1 rightRead ∧
                                  Cont leftRead rightRead midpointRead ∧
                                    Cont midpointRead Q toleranceRead ∧
                                      Cont toleranceRead E sealRead ∧
                                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro r0Unary r1Unary s0Unary s1Unary accepted leftRoute rightRoute midpointRoute
    toleranceRoute sealRoute sealPkg
  obtain ⟨_cert, midpointUnary, toleranceUnary, sealUnary⟩ := accepted
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed r0Unary s0Unary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed r1Unary s1Unary rightRoute
  exact
    ⟨leftUnary, rightUnary, midpointUnary, toleranceUnary, sealUnary, leftRoute,
      rightRoute, midpointRoute, toleranceRoute, sealRoute, sealPkg⟩

end BEDC.Derived.RegularCauchyMidpointUp

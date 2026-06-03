import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceRootHausdorffTransport [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead directedRead toleranceRead
      transportedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont X K0 compactRead →
        Cont compactRead D0 directedRead →
          Cont directedRead R toleranceRead →
            Cont toleranceRead Hs transportedRead →
              Cont transportedRead C namedRead →
                PkgSig bundle P pkg →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row K0 ∨ hsame row D0 ∨ hsame row R ∨
                          hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                            hsame row compactRead ∨ hsame row directedRead ∨
                              hsame row toleranceRead ∨ hsame row transportedRead ∨
                                hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont X K0 compactRead ∧
                          Cont compactRead D0 directedRead ∧
                            Cont directedRead R toleranceRead ∧
                              Cont toleranceRead Hs transportedRead ∧
                                Cont transportedRead C namedRead ∧ PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory compactRead ∧ UnaryHistory directedRead ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory transportedRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier compactRoute directedRoute toleranceRoute transportedRoute namedRoute
    _provenancePkg namedPkg
  obtain ⟨xUnary, k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, _d1Unary, rUnary,
    hsUnary, cUnary, _pUnary, _mUnary, _carrierPkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary k0Unary compactRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed compactUnary d0Unary directedRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed directedUnary rUnary toleranceRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed toleranceUnary hsUnary transportedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed transportedUnary cUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row D0 ∨ hsame row R ∨
              hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                hsame row compactRead ∨ hsame row directedRead ∨
                  hsame row toleranceRead ∨ hsame row transportedRead ∨
                    hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X K0 compactRead ∧
              Cont compactRead D0 directedRead ∧ Cont directedRead R toleranceRead ∧
                Cont toleranceRead Hs transportedRead ∧ Cont transportedRead C namedRead ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, directedRoute, toleranceRoute, transportedRoute,
          namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, compactUnary, directedUnary, toleranceUnary, transportedUnary, namedUnary⟩

end BEDC.Derived.HyperspaceUp

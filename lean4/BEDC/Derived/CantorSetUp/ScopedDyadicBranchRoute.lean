import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetScopedDyadicBranchRoute [AskSetup] [PackageSetup]
    {pref gap nested endpoint regular realSeal _transport _replay provenance localName branchRead
      dyadicRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory pref ->
      UnaryHistory gap ->
        UnaryHistory endpoint ->
          UnaryHistory regular ->
            UnaryHistory realSeal ->
              UnaryHistory provenance ->
                Cont pref gap nested ->
                  Cont nested endpoint branchRead ->
                    Cont branchRead regular dyadicRead ->
                      Cont dyadicRead realSeal sealedRead ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle localName pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row pref ∨ hsame row gap ∨ hsame row nested ∨
                                    hsame row endpoint ∨ hsame row regular ∨
                                      hsame row realSeal ∨ hsame row sealedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory branchRead ∧ UnaryHistory dyadicRead ∧
                                UnaryHistory sealedRead ∧
                                  hsame sealedRead (append dyadicRead realSeal) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro prefUnary gapUnary endpointUnary regularUnary sealUnary _provenanceUnary nestedRoute
    branchRoute dyadicRoute sealRoute provenancePkg localNamePkg
  have nestedUnary : UnaryHistory nested :=
    unary_cont_closed prefUnary gapUnary nestedRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed nestedUnary endpointUnary branchRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed branchUnary regularUnary dyadicRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed dyadicUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row pref ∨ hsame row gap ∨ hsame row nested ∨ hsame row endpoint ∨
              hsame row regular ∨ hsame row realSeal ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  have sealedSame : hsame sealedRead (append dyadicRead realSeal) := by
    cases sealRoute
    rfl
  exact ⟨cert, branchUnary, dyadicUnary, sealedUnary, sealedSame⟩

end BEDC.Derived.CantorSetUp

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

theorem CantorSetScopedRealSealRoute [AskSetup] [PackageSetup]
    {pref gap nested endpoint regular realSeal transport replay provenance localName membershipRead
      regularRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory pref ->
      UnaryHistory gap ->
        UnaryHistory endpoint ->
          UnaryHistory regular ->
            UnaryHistory realSeal ->
              Cont pref gap nested ->
                Cont nested endpoint membershipRead ->
                  Cont membershipRead regular regularRead ->
                    Cont regularRead realSeal sealedRead ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle localName pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row pref ∨ hsame row gap ∨ hsame row nested ∨
                                  hsame row endpoint ∨ hsame row regular ∨ hsame row realSeal ∨
                                    hsame row transport ∨ hsame row replay ∨
                                      hsame row provenance ∨ hsame row localName ∨
                                        hsame row sealedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont pref gap nested ∧
                                  Cont nested endpoint membershipRead ∧
                                    Cont membershipRead regular regularRead ∧
                                      Cont regularRead realSeal sealedRead ∧
                                        PkgSig bundle provenance pkg)
                              hsame ∧
                            UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro prefUnary gapUnary endpointUnary regularUnary realSealUnary nestedRoute membershipRoute
    regularRoute sealRoute provenancePkg _localNamePkg
  have nestedUnary : UnaryHistory nested :=
    unary_cont_closed prefUnary gapUnary nestedRoute
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed nestedUnary endpointUnary membershipRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed membershipUnary regularUnary regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularReadUnary realSealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row pref ∨ hsame row gap ∨ hsame row nested ∨ hsame row endpoint ∨
              hsame row regular ∨ hsame row realSeal ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont pref gap nested ∧ Cont nested endpoint membershipRead ∧
              Cont membershipRead regular regularRead ∧ Cont regularRead realSeal sealedRead ∧
                PkgSig bundle provenance pkg)
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
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, nestedRoute, membershipRoute, regularRoute, sealRoute, provenancePkg⟩
  }
  exact ⟨cert, sealedUnary⟩

end BEDC.Derived.CantorSetUp

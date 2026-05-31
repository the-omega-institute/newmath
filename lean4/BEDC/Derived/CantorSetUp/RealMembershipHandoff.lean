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

theorem CantorSetCarrier_real_membership_handoff [AskSetup] [PackageSetup]
    {T G I D R E membershipRead regularRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G I ->
      Cont I D membershipRead ->
        Cont membershipRead R regularRead ->
          Cont regularRead E sealedRead ->
            PkgSig bundle E pkg ->
              UnaryHistory T ->
                UnaryHistory G ->
                  UnaryHistory D ->
                    UnaryHistory R ->
                      UnaryHistory E ->
                        SemanticNameCert
                            (fun row : BHist => hsame row E ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨
                                hsame row R ∨ hsame row E)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont membershipRead R regularRead ∧
                                Cont regularRead E sealedRead ∧ PkgSig bundle E pkg)
                            hsame ∧
                          UnaryHistory membershipRead ∧ UnaryHistory regularRead ∧
                            UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixRoute membershipRoute regularRoute sealRoute packageE prefixUnary gapUnary
    endpointUnary regularUnary sealUnary
  have intervalUnary : UnaryHistory I :=
    unary_cont_closed prefixUnary gapUnary prefixRoute
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed intervalUnary endpointUnary membershipRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed membershipUnary regularUnary regularRoute
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont membershipRead R regularRead ∧
              Cont regularRead E sealedRead ∧ PkgSig bundle E pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro E ⟨hsame_refl E, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regularRoute, sealRoute, packageE⟩
  }
  exact ⟨cert, membershipUnary, regularReadUnary, sealedReadUnary⟩

end BEDC.Derived.CantorSetUp

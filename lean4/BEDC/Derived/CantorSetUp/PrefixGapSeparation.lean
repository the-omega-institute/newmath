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

theorem CantorSetCarrier_prefix_gap_separation [AskSetup] [PackageSetup]
    {T G I D E prefixRead gapRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead →
      Cont prefixRead I gapRead →
        Cont gapRead D endpointRead →
          PkgSig bundle E pkg →
            UnaryHistory T →
              UnaryHistory G →
                UnaryHistory I →
                  UnaryHistory D →
                    SemanticNameCert
                        (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨
                            hsame row I ∨ hsame row gapRead ∨ hsame row D)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont prefixRead I gapRead ∧
                            Cont gapRead D endpointRead ∧ PkgSig bundle E pkg)
                        hsame ∧
                      UnaryHistory prefixRead ∧ UnaryHistory gapRead ∧
                        UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixRoute gapRoute endpointRoute packageE prefixUnary gapUnary intervalUnary endpointUnary
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed prefixUnary gapUnary prefixRoute
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed prefixReadUnary intervalUnary gapRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed gapReadUnary endpointUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row prefixRead ∨ hsame row I ∨
              hsame row gapRead ∨ hsame row D)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont prefixRead I gapRead ∧
              Cont gapRead D endpointRead ∧ PkgSig bundle E pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gapRead ⟨hsame_refl gapRead, gapReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gapRoute, endpointRoute, packageE⟩
  }
  exact ⟨cert, prefixReadUnary, gapReadUnary, endpointReadUnary⟩

end BEDC.Derived.CantorSetUp

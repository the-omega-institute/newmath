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

theorem CantorSetDeletedGapDensityRefusal [AskSetup] [PackageSetup]
    {T G I D R E H K P N gapRead endpointRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G →
      UnaryHistory I →
        UnaryHistory D →
          UnaryHistory R →
            Cont G I gapRead →
              Cont gapRead D endpointRead →
                Cont endpointRead R regularRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row G ∨ hsame row gapRead ∨ hsame row endpointRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont G I gapRead ∧
                              Cont gapRead D endpointRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory gapRead ∧ UnaryHistory endpointRead ∧
                          UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro gapUnary intervalUnary endpointUnary regularUnary gapRoute endpointRoute regularRoute
    provenancePkg namePkg
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed gapUnary intervalUnary gapRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed gapReadUnary endpointUnary endpointRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointReadUnary regularUnary regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row gapRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G I gapRead ∧ Cont gapRead D endpointRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gapRoute, endpointRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, gapReadUnary, endpointReadUnary, regularReadUnary⟩

end BEDC.Derived.CantorSetUp

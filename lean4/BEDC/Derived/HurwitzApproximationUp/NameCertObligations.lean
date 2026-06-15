import BEDC.Derived.HurwitzApproximationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HurwitzApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HurwitzApproximationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Q A C F S D R E T U P N inputRead prefixRead convergentRead neighborRead
      budgetRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory X ∧ UnaryHistory Q ∧ UnaryHistory A ∧ UnaryHistory C ∧
      UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧
        UnaryHistory E) →
      Cont X Q inputRead →
        Cont inputRead A prefixRead →
          Cont prefixRead C convergentRead →
            Cont convergentRead F neighborRead →
              Cont neighborRead D budgetRead →
                Cont budgetRead R outputRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row Q ∨ hsame row A ∨
                              hsame row C ∨ hsame row F ∨ hsame row S ∨
                                hsame row D ∨ hsame row R ∨ hsame row E ∨
                                  hsame row outputRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory outputRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rows inputRoute prefixRoute convergentRoute neighborRoute budgetRoute outputRoute
    provenancePkg namePkg
  obtain ⟨xUnary, qUnary, aUnary, cUnary, fUnary, _sUnary, dUnary, rUnary,
    _eUnary⟩ := rows
  have inputUnary : UnaryHistory inputRead :=
    unary_cont_closed xUnary qUnary inputRoute
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed inputUnary aUnary prefixRoute
  have convergentUnary : UnaryHistory convergentRead :=
    unary_cont_closed prefixUnary cUnary convergentRoute
  have neighborUnary : UnaryHistory neighborRead :=
    unary_cont_closed convergentUnary fUnary neighborRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed neighborUnary dUnary budgetRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed budgetUnary rUnary outputRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Q ∨ hsame row A ∨ hsame row C ∨
              hsame row F ∨ hsame row S ∨ hsame row D ∨ hsame row R ∨
                hsame row E ∨ hsame row outputRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro outputRead ⟨hsame_refl outputRead, outputUnary⟩
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
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, outputUnary⟩

end BEDC.Derived.HurwitzApproximationUp

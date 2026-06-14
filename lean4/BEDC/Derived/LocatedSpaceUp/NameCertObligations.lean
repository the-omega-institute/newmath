import BEDC.Derived.LocatedSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X R A G W Q E H C P N requestRead gapRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory X ∧ UnaryHistory R ∧ UnaryHistory A ∧ UnaryHistory G ∧
      UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg) →
      Cont X R requestRead →
        Cont A G gapRead →
          Cont requestRead Q sealRead →
            Cont gapRead E sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row R ∨ hsame row A ∨ hsame row G ∨
                        hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont X R requestRead ∧ Cont A G gapRead ∧
                        PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rows requestRoute gapRoute _sealFromRequest sealFromGap sealPkg
  obtain ⟨xUnary, rUnary, aUnary, gUnary, _wUnary, qUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _pPkg⟩ := rows
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed xUnary rUnary requestRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed aUnary gUnary gapRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed gapUnary eUnary sealFromGap
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row R ∨ hsame row A ∨ hsame row G ∨
              hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X R requestRead ∧ Cont A G gapRead ∧
              PkgSig bundle sealRead pkg)
          hsame := by
    exact {
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
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, requestRoute, gapRoute, sealPkg⟩
    }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.LocatedSpaceUp

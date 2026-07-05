import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RiemannSeriesTheoremUp : Type where
  | mk (S Ppos Pneg W A T D E H C Q N : BHist) : RiemannSeriesTheoremUp
  deriving DecidableEq

end BEDC.Derived

namespace BEDC.Derived.RiemannSeriesTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RiemannSeriesTheoremCarrier [AskSetup] [PackageSetup]
    (S Ppos Pneg W A T D E H C Q N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory Ppos ∧ UnaryHistory Pneg ∧ UnaryHistory W ∧
    UnaryHistory A ∧ UnaryHistory T ∧ UnaryHistory D ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory N ∧
        PkgSig bundle N pkg

theorem RiemannSeriesTheoremCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {S Ppos Pneg W A T D E H C Q N scheduleRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSeriesTheoremCarrier S Ppos Pneg W A T D E H C Q N bundle pkg →
      Cont A T scheduleRead →
        Cont scheduleRead E endpointRead →
          PkgSig bundle endpointRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row Ppos ∨ hsame row Pneg ∨ hsame row W ∨
                    hsame row A ∨ hsame row T ∨ hsame row D ∨ hsame row E ∨
                      hsame row endpointRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont A T scheduleRead ∧
                    Cont scheduleRead E endpointRead ∧ PkgSig bundle endpointRead pkg)
                hsame ∧ UnaryHistory scheduleRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: RiemannSeriesTheoremCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier scheduleRoute endpointRoute endpointPkg
  obtain ⟨_sUnary, _posUnary, _negUnary, _wUnary, aUnary, tUnary, _dUnary, eUnary,
    _hUnary, _cUnary, _qUnary, _nUnary, _pkgAtN⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed aUnary tUnary scheduleRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed scheduleUnary eUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Ppos ∨ hsame row Pneg ∨ hsame row W ∨
              hsame row A ∨ hsame row T ∨ hsame row D ∨ hsame row E ∨
                hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A T scheduleRead ∧
              Cont scheduleRead E endpointRead ∧ PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
      repeat (first | exact sourceRow.left | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, scheduleRoute, endpointRoute, endpointPkg⟩
  }
  exact ⟨cert, scheduleUnary, endpointUnary⟩

end BEDC.Derived.RiemannSeriesTheoremUp

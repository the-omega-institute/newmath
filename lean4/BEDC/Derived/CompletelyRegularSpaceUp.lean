import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletelyRegularSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletelyRegularSpaceCarrier [AskSetup] [PackageSetup]
    (topology regular request separator transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory topology ∧ UnaryHistory regular ∧ UnaryHistory request ∧
    UnaryHistory separator ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont topology regular request ∧
        Cont request separator replay ∧ PkgSig bundle provenance pkg

theorem CompletelyRegularSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T R C F H K P N separatorRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletelyRegularSpaceCarrier T R C F H K P N bundle pkg →
      Cont K N separatorRead →
        SemanticNameCert
            (fun row : BHist => hsame row separatorRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row T ∨ hsame row R ∨ hsame row C ∨ hsame row F ∨ hsame row H ∨
                hsame row K ∨ hsame row P ∨ hsame row N ∨ hsame row separatorRead)
            (fun row : BHist =>
              UnaryHistory row ∧ CompletelyRegularSpaceCarrier T R C F H K P N bundle pkg ∧
                Cont K N separatorRead)
            hsame ∧ UnaryHistory separatorRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierData separatorRoute
  have carrierOriginal :
      CompletelyRegularSpaceCarrier T R C F H K P N bundle pkg := carrierData
  obtain ⟨_tUnary, _rUnary, _cUnary, _fUnary, _hUnary, kUnary, _pUnary, nUnary,
    _requestRoute, _replayRoute, _pkgProvenance⟩ := carrierData
  have separatorUnary : UnaryHistory separatorRead :=
    unary_cont_closed kUnary nUnary separatorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row R ∨ hsame row C ∨ hsame row F ∨ hsame row H ∨
              hsame row K ∨ hsame row P ∨ hsame row N ∨ hsame row separatorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ CompletelyRegularSpaceCarrier T R C F H K P N bundle pkg ∧
              Cont K N separatorRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separatorRead ⟨hsame_refl separatorRead, separatorUnary⟩
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
      exact ⟨sourceRow.right, carrierOriginal, separatorRoute⟩
  }
  exact ⟨cert, separatorUnary⟩

end BEDC.Derived.CompletelyRegularSpaceUp

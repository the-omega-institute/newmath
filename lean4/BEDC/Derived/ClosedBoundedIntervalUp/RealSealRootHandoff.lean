import BEDC.Derived.ClosedBoundedIntervalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_real_seal_root_handoff [AskSetup] [PackageSetup]
    {L U O Q D S R E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L -> UnaryHistory U -> UnaryHistory O -> UnaryHistory Q ->
      UnaryHistory D -> UnaryHistory S -> UnaryHistory R -> UnaryHistory E ->
        UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
          Cont Q D S ->
            Cont S R E ->
              Cont S R sealRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle sealRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row R ∨ hsame row E ∨ Cont S R sealRead)
                        (fun row : BHist =>
                          PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg ∧
                            hsame row sealRead)
                        hsame ∧
                      UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧
                        UnaryHistory sealRead ∧ Cont Q D S ∧ Cont S R sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary _oUnary qUnary dUnary sUnary rUnary eUnary _hUnary _cUnary
    _pUnary _nUnary qdStream streamReadbackSeal streamReadbackHandoff pPkg handoffPkg
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sUnary rUnary streamReadbackHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row S ∨ hsame row R ∨ hsame row E ∨ Cont S R sealRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg ∧ hsame row sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead
        ⟨hsame_refl sealRead, sealReadUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr streamReadbackHandoff))
    ledger_sound := by
      intro _row source
      exact ⟨pPkg, handoffPkg, source.left⟩
  }
  exact
    ⟨cert, sUnary, rUnary, eUnary, sealReadUnary, qdStream, streamReadbackHandoff⟩

end BEDC.Derived.ClosedBoundedIntervalUp

import BEDC.Derived.RegularCauchyTailFiberUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyTailFiberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailFiberPacket_completion_handoff_scope [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      Cont t a completion →
        PkgSig bundle completion pkg →
          SemanticNameCert
            (fun row : BHist =>
              RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg ∧
                hsame row completion)
            (fun row : BHist =>
              Cont d0 d1 t ∧ Cont t a row ∧ PkgSig bundle completion pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completion pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet completionRoute completionPkg
  have packetWitness := packet
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, _d0Unary, _d1Unary, tUnary,
    aUnary, _hUnary, _cUnary, _pUnary, _nUnary, _hRoute, _cRoute, tailRoute,
    _packetSealRoute, _packetPkg⟩ := packet
  have sourceCompletion :
      (fun row : BHist =>
        RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg ∧
          hsame row completion) completion := by
    exact And.intro packetWitness (hsame_refl completion)
  exact {
    core := {
      carrier_inhabited := Exists.intro completion sourceCompletion
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        And.intro tailRoute
          (And.intro (cont_result_hsame_transport completionRoute (hsame_symm source.right))
            completionPkg)
    ledger_sound := by
      intro row source
      have completionUnary : UnaryHistory completion :=
        unary_cont_closed tUnary aUnary completionRoute
      exact And.intro (unary_transport completionUnary (hsame_symm source.right)) completionPkg
  }

end BEDC.Derived.RegularCauchyTailFiberUp

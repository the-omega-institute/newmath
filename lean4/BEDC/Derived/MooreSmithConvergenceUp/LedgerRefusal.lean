import BEDC.Derived.MooreSmithConvergenceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MooreSmithConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MooreSmithConvergencePacket_ledger_refusal [AskSetup] [PackageSetup]
    {D V U C B R L H K P N refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg ->
      Cont K N refusedRead ->
        PkgSig bundle refusedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row refusedRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row refusedRead ∧ Cont K N refusedRead)
              (fun row : BHist => hsame row refusedRead ∧ PkgSig bundle refusedRead pkg)
              hsame ∧
            UnaryHistory refusedRead ∧ Cont K N refusedRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle refusedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet refusedRoute refusedPkg
  obtain ⟨_dUnary, _vUnary, _uUnary, _cUnary, _bUnary, _rUnary, _lUnary, _hUnary,
    kUnary, nUnary, _dvu, _ucb, _brl, provenancePkg⟩ := packet
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed kUnary nUnary refusedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusedRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusedRead ∧ Cont K N refusedRead)
          (fun row : BHist => hsame row refusedRead ∧ PkgSig bundle refusedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro refusedRead
          ⟨hsame_refl refusedRead, refusedUnary⟩
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
          intro row other sameRows source
          have otherSame : hsame other refusedRead :=
            hsame_trans (hsame_symm sameRows) source.left
          have otherUnary : UnaryHistory other :=
            unary_transport source.right sameRows
          exact ⟨otherSame, otherUnary⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, refusedRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, refusedPkg⟩
    }
  exact ⟨cert, refusedUnary, refusedRoute, provenancePkg, refusedPkg⟩

end BEDC.Derived.MooreSmithConvergenceUp

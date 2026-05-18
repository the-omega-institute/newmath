import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_normalization_frontier_consumer_lock
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead frontierRead lockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont A C outputRead ->
        Cont outputRead G frontierRead ->
          Cont frontierRead N lockedRead ->
            PkgSig bundle lockedRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N
                      bundle pkg ∧ hsame row lockedRead)
                  (fun row : BHist =>
                    hsame row lockedRead ∧ Cont A C outputRead ∧
                      Cont outputRead G frontierRead ∧ Cont frontierRead N lockedRead)
                  (fun row : BHist =>
                    hsame row lockedRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle lockedRead pkg)
                  hsame ∧
                UnaryHistory outputRead ∧ UnaryHistory frontierRead ∧
                  UnaryHistory lockedRead ∧ Cont A C outputRead ∧
                    Cont outputRead G frontierRead ∧ Cont frontierRead N lockedRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle lockedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier outputRoute frontierRoute lockedRoute lockedPkg
  have carrierPacket :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg :=
    carrier
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, unaryA,
      _unaryH, unaryC, _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      _sameLedger, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryA unaryC outputRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed outputUnary unaryG frontierRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed frontierUnary unaryN lockedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
              hsame row lockedRead)
          (fun row : BHist =>
            hsame row lockedRead ∧ Cont A C outputRead ∧
              Cont outputRead G frontierRead ∧ Cont frontierRead N lockedRead)
          (fun row : BHist =>
            hsame row lockedRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle lockedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro lockedRead ⟨carrierPacket, hsame_refl lockedRead⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, outputRoute, frontierRoute, lockedRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, lockedPkg⟩
    }
  exact
    ⟨cert, outputUnary, frontierUnary, lockedUnary, outputRoute, frontierRoute,
      lockedRoute, provenancePkg, lockedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

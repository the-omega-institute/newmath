import BEDC.Derived.InterHistTransportSealUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.InterHistTransportSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem InterHistTransportSeal_nonescape [AskSetup] [PackageSetup]
    {x : InterHistTransportSealUp} {A B L I O R H C P N LI OR sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    interHistTransportSealFields x = [A, B, L, I, O, R, H, C, P, N] ->
      Cont L I LI ->
        Cont LI O OR ->
          Cont OR R sealRow ->
            UnaryHistory L ->
              UnaryHistory I ->
                UnaryHistory O ->
                  UnaryHistory R ->
                    UnaryHistory N ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row sealRow ∧ Cont L I LI ∧ Cont LI O OR ∧
                                Cont OR R sealRow)
                            (fun row : BHist => hsame row sealRow ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory LI ∧ UnaryHistory OR ∧ UnaryHistory sealRow := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fields localityInvariant invariantObserver observerRoute localityUnary invariantUnary
    observerUnary routeUnary _nameUnary namePkg
  have _fields :
      interHistTransportSealFields x = [A, B, L, I, O, R, H, C, P, N] := fields
  have liUnary : UnaryHistory LI :=
    unary_cont_closed localityUnary invariantUnary localityInvariant
  have orUnary : UnaryHistory OR :=
    unary_cont_closed liUnary observerUnary invariantObserver
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed orUnary routeUnary observerRoute
  have sourceAtSeal : hsame sealRow sealRow ∧ UnaryHistory sealRow :=
    ⟨hsame_refl sealRow, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sealRow ∧ Cont L I LI ∧ Cont LI O OR ∧ Cont OR R sealRow)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceAtSeal
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
      exact ⟨source.left, localityInvariant, invariantObserver, observerRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact ⟨cert, liUnary, orUnary, sealUnary⟩

end BEDC.Derived.InterHistTransportSealUp

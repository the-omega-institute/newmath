import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem OnticStateScopedClosurePackage [AskSetup] [PackageSetup]
    {S A K R H C P N sourceRead residueRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
        [S, A, K, R, H, C, P, N] ->
      Cont S A sourceRead ->
        Cont K R residueRead ->
          Cont sourceRead residueRead scopedRead ->
            PkgSig bundle scopedRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  hsame row scopedRead ∧
                    ∃ packet : OnticStateUp,
                      packet = OnticStateUp.mk S A K R H C P N ∧
                        FieldFaithful.fields packet = [S, A, K, R, H, C, P, N])
                (fun row : BHist =>
                  Cont S A sourceRead ∧ Cont K R residueRead ∧
                    Cont sourceRead residueRead row)
                (fun row : BHist => hsame row scopedRead ∧ PkgSig bundle scopedRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert FieldFaithful
  intro fields sourceRoute residueRoute scopedRoute scopedPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro scopedRead
          (And.intro (hsame_refl scopedRead)
            (Exists.intro (OnticStateUp.mk S A K R H C P N)
              (And.intro rfl fields)))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact
        And.intro sourceRoute
          (And.intro residueRoute
            (cont_result_hsame_transport scopedRoute (hsame_symm source.left)))
    ledger_sound := by
      intro _row source
      exact And.intro source.left scopedPkg
  }

end BEDC.Derived.OnticStateUp

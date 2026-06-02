import BEDC.Derived.RepresentedSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_realizer_scope [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduledRead
      relationRead targetRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg ->
      Cont name schedule scheduledRead ->
        Cont scheduledRead relation relationRead ->
          Cont target localName targetRead ->
            Cont relationRead targetRead scopedRead ->
              PkgSig bundle scopedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                        hsame row target ∨ hsame row scheduledRead ∨
                          hsame row relationRead ∨ hsame row targetRead ∨
                            hsame row scopedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle scopedRead pkg)
                    hsame ∧
                  UnaryHistory scheduledRead ∧ UnaryHistory relationRead ∧
                    UnaryHistory targetRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scheduleRoute relationRoute targetRoute scopedRoute scopedPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduledReadUnary : UnaryHistory scheduledRead :=
    unary_cont_closed nameUnary scheduleUnary scheduleRoute
  have relationReadUnary : UnaryHistory relationRead :=
    unary_cont_closed scheduledReadUnary relationUnary relationRoute
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary localNameUnary targetRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed relationReadUnary targetReadUnary scopedRoute
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, scopedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row scheduledRead ∨ hsame row relationRead ∨
                hsame row targetRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceScoped
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, scopedPkg⟩
  }
  exact ⟨cert, scheduledReadUnary, relationReadUnary, targetReadUnary, scopedReadUnary⟩

end BEDC.Derived.RepresentedSpaceUp

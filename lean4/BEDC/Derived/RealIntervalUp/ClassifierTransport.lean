import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalClassifierTransport [AskSetup] [PackageSetup]
    {L U E D W R S H C P N L' U' E' D' W' R' S' H' C' P' N' sealRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory U →
        UnaryHistory E →
          UnaryHistory R →
            UnaryHistory H' →
              hsame L L' →
                hsame U U' →
                  hsame E E' →
                    hsame D D' →
                      hsame W W' →
                        hsame R R' →
                          Cont E R sealRead →
                            Cont sealRead H' replayRead →
                              PkgSig bundle P' pkg →
                                PkgSig bundle N' pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row E' ∨ hsame row sealRead ∨
                                            hsame row replayRead) ∧
                                          UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row L' ∨ hsame row U' ∨ hsame row E' ∨
                                          hsame row D' ∨ hsame row W' ∨ hsame row R' ∨
                                            hsame row sealRead ∨ hsame row S' ∨
                                              hsame row H' ∨ hsame row C' ∨
                                                hsame row P' ∨ hsame row N' ∨
                                                  hsame row replayRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont E R sealRead ∧
                                          Cont sealRead H' replayRead ∧
                                            PkgSig bundle P' pkg ∧ PkgSig bundle N' pkg)
                                      hsame ∧
                                    UnaryHistory E' ∧ UnaryHistory sealRead ∧
                                      UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro _unaryL _unaryU unaryE unaryR unaryH'
  intro _sameL _sameU sameE _sameD _sameW _sameR sealRoute replayRoute pkgP' pkgN'
  have unaryE' : UnaryHistory E' :=
    unary_transport unaryE sameE
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryE unaryR sealRoute
  have unaryReplay : UnaryHistory replayRead :=
    unary_cont_closed unarySeal unaryH' replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row E' ∨ hsame row sealRead ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row L' ∨ hsame row U' ∨ hsame row E' ∨ hsame row D' ∨
              hsame row W' ∨ hsame row R' ∨ hsame row sealRead ∨ hsame row S' ∨
                hsame row H' ∨ hsame row C' ∨ hsame row P' ∨ hsame row N' ∨
                  hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E R sealRead ∧ Cont sealRead H' replayRead ∧
              PkgSig bundle P' pkg ∧ PkgSig bundle N' pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E' ⟨Or.inl (hsame_refl E'), unaryE'⟩
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
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases source.left with
          | inl sameE' =>
              exact Or.inl (lift sameE')
          | inr tail =>
              cases tail with
              | inl sameSeal =>
                  exact Or.inr (Or.inl (lift sameSeal))
              | inr sameReplay =>
                  exact Or.inr (Or.inr (lift sameReplay))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameE' =>
          exact Or.inr (Or.inr (Or.inl sameE'))
      | inr tail =>
          cases tail with
          | inl sameSeal =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inl sameSeal))))))
          | inr sameReplay =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr sameReplay))))))))))
                    )
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, replayRoute, pkgP', pkgN'⟩
  }
  exact ⟨cert, unaryE', unarySeal, unaryReplay⟩

end BEDC.Derived.RealIntervalUp

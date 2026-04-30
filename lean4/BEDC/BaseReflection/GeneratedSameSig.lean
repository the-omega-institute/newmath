import BEDC.BaseReflection.PackageReflection

namespace BEDC.BaseReflection

structure GeneratedSameSig (s : BaseReflectionSetup) (P : s.Pi) (h k : s.Hist) : Type where
  leftSigObj : s.SigObj
  rightSigObj : s.SigObj
  leftEvidence : s.Evidence
  rightEvidence : s.Evidence
  leftSig : s.SigGen P h leftSigObj leftEvidence
  rightSig : s.SigGen P k rightSigObj rightEvidence
  sigSame : s.hsame leftSigObj rightSigObj

def GeneratedSameSig_from_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist} {x y : s.SigObj}
    {ex ey : s.Evidence} :
    s.SigGen P h x ex -> s.SigGen P k y ey -> s.hsame x y ->
      GeneratedSameSig s P h k := by
  intro left right same
  exact {
    leftSigObj := x
    rightSigObj := y
    leftEvidence := ex
    rightEvidence := ey
    leftSig := left
    rightSig := right
    sigSame := same
  }

theorem GeneratedSameSig_refl_nonempty_from_sig
    {s : BaseReflectionSetup} {P : s.Pi} {h : s.Hist} {x : s.SigObj} {e : s.Evidence}
    (eqv : HSameEquiv s) :
    s.SigGen P h x e → Nonempty (GeneratedSameSig s P h h) := by
  intro sig
  exact Nonempty.intro {
    leftSigObj := x
    rightSigObj := x
    leftEvidence := e
    rightEvidence := e
    leftSig := sig
    rightSig := sig
    sigSame := eqv.refl x
  }

theorem GeneratedSameSig_hsame
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    s.hsame gen.leftSigObj gen.rightSigObj := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact sigSame

theorem GeneratedSameSig_left_witness
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    ∃ x : s.SigObj, ∃ e : s.Evidence, s.SigGen P h x e := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro leftSigObj (Exists.intro leftEvidence leftSig)

theorem GeneratedSameSig_right_witness
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    exists y : s.SigObj, exists e : s.Evidence, s.SigGen P k y e := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro rightSigObj (Exists.intro rightEvidence rightSig)

theorem GeneratedSameSig_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    ∃ x : s.SigObj, ∃ y : s.SigObj,
      ∃ leftEvidence : s.Evidence, ∃ rightEvidence : s.Evidence,
        s.SigGen P h x leftEvidence /\
        s.SigGen P k y rightEvidence /\ s.hsame x y := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro leftSigObj
        (Exists.intro rightSigObj
          (Exists.intro leftEvidence
            (Exists.intro rightEvidence
              (And.intro leftSig (And.intro rightSig sigSame)))))

theorem GeneratedSameSig_swap_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (eqv : HSameEquiv s) (gen : GeneratedSameSig s P h k) :
    exists y : s.SigObj, exists x : s.SigObj,
      exists rightEvidence : s.Evidence, exists leftEvidence : s.Evidence,
        s.SigGen P k y rightEvidence /\
        s.SigGen P h x leftEvidence /\ s.hsame y x := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro rightSigObj
        (Exists.intro leftSigObj
          (Exists.intro rightEvidence
            (Exists.intro leftEvidence
              (And.intro rightSig (And.intro leftSig (eqv.symm sigSame))))))

def GeneratedSameSig_symm
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (eqv : HSameEquiv s) :
    GeneratedSameSig s P h k -> GeneratedSameSig s P k h := by
  intro gen
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact {
        leftSigObj := rightSigObj
        rightSigObj := leftSigObj
        leftEvidence := rightEvidence
        rightEvidence := leftEvidence
        leftSig := rightSig
        rightSig := leftSig
        sigSame := eqv.symm sigSame
      }

theorem GeneratedSameSig_symm_nonempty
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (eqv : HSameEquiv s) :
    Nonempty (GeneratedSameSig s P h k) → Nonempty (GeneratedSameSig s P k h) := by
  intro hgen
  cases hgen with
  | intro gen =>
      cases gen with
      | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
          exact Nonempty.intro {
            leftSigObj := rightSigObj
            rightSigObj := leftSigObj
            leftEvidence := rightEvidence
            rightEvidence := leftEvidence
            leftSig := rightSig
            rightSig := leftSig
            sigSame := eqv.symm sigSame
          }

theorem GeneratedSameSig_trans_nonempty_under_determinacy
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s)
    (det : forall {h : s.Hist} {x y : s.SigObj} {ex ey : s.Evidence},
      s.SigGen P h x ex -> s.SigGen P h y ey -> s.hsame x y)
    {h k l : s.Hist} :
    Nonempty (GeneratedSameSig s P h k) ->
      Nonempty (GeneratedSameSig s P k l) ->
        Nonempty (GeneratedSameSig s P h l) := by
  intro left right
  cases left with
  | intro leftGen =>
      cases right with
      | intro rightGen =>
          cases leftGen with
          | mk leftSigObj midSigObj leftEvidence midEvidence leftSig midSig leftSame =>
              cases rightGen with
              | mk midSigObj' rightSigObj midEvidence' rightEvidence midSig' rightSig rightSame =>
                  exact Nonempty.intro {
                    leftSigObj := leftSigObj
                    rightSigObj := rightSigObj
                    leftEvidence := leftEvidence
                    rightEvidence := rightEvidence
                    leftSig := leftSig
                    rightSig := rightSig
                    sigSame := eqv.trans leftSame (eqv.trans (det midSig midSig') rightSame)
                  }

def GeneratedSameSig_trans_under_determinacy
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s)
    (det : forall {h : s.Hist} {x y : s.SigObj} {ex ey : s.Evidence},
      s.SigGen P h x ex -> s.SigGen P h y ey -> s.hsame x y)
    {h k l : s.Hist} :
    GeneratedSameSig s P h k -> GeneratedSameSig s P k l -> GeneratedSameSig s P h l := by
  intro left right
  cases left with
  | mk leftSigObj midSigObj leftEvidence midEvidence leftSig midSig leftSame =>
      cases right with
      | mk midSigObj' rightSigObj midEvidence' rightEvidence midSig' rightSig rightSame =>
          exact {
            leftSigObj := leftSigObj
            rightSigObj := rightSigObj
            leftEvidence := leftEvidence
            rightEvidence := rightEvidence
            leftSig := leftSig
            rightSig := rightSig
            sigSame := eqv.trans leftSame (eqv.trans (det midSig midSig') rightSame)
          }

theorem GeneratedSameSig_trans_nonempty_direct_under_determinacy
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s)
    (det : forall {h : s.Hist} {x y : s.SigObj} {ex ey : s.Evidence},
      s.SigGen P h x ex -> s.SigGen P h y ey -> s.hsame x y)
    {h k l : s.Hist} :
    Nonempty (GeneratedSameSig s P h k) ->
      Nonempty (GeneratedSameSig s P k l) ->
        Nonempty (GeneratedSameSig s P h l) := by
  intro left right
  cases left with
  | intro leftGen =>
      cases right with
      | intro rightGen =>
          exact Nonempty.intro
            (GeneratedSameSig_trans_under_determinacy eqv det leftGen rightGen)

theorem GeneratedSameSig_chain_witnesses_under_determinacy
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s)
    (det : forall {h : s.Hist} {x y : s.SigObj} {ex ey : s.Evidence},
      s.SigGen P h x ex -> s.SigGen P h y ey -> s.hsame x y)
    {h k l : s.Hist} :
    GeneratedSameSig s P h k -> GeneratedSameSig s P k l ->
      exists x : s.SigObj, exists z : s.SigObj,
        exists ex : s.Evidence, exists ez : s.Evidence,
          s.SigGen P h x ex /\ s.SigGen P l z ez /\ s.hsame x z := by
  intro left right
  cases left with
  | mk leftSigObj midSigObj leftEvidence midEvidence leftSig midSig leftSame =>
      cases right with
      | mk midSigObj' rightSigObj midEvidence' rightEvidence midSig' rightSig rightSame =>
          exact Exists.intro leftSigObj
            (Exists.intro rightSigObj
              (Exists.intro leftEvidence
                (Exists.intro rightEvidence
                    (And.intro leftSig
                    (And.intro rightSig
                      (eqv.trans leftSame (eqv.trans (det midSig midSig') rightSame)))))))

theorem GeneratedSameSig_trans_witness_object_under_determinacy
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s)
    (det : forall {h : s.Hist} {x y : s.SigObj} {ex ey : s.Evidence},
      s.SigGen P h x ex -> s.SigGen P h y ey -> s.hsame x y)
    {h k l : s.Hist} :
    GeneratedSameSig s P h k -> GeneratedSameSig s P k l ->
      exists x : s.SigObj, exists z : s.SigObj, exists ex : s.Evidence, exists ez : s.Evidence,
        s.SigGen P h x ex /\ s.SigGen P l z ez /\ s.hsame x z := by
  intro left right
  cases left with
  | mk leftSigObj midSigObj leftEvidence midEvidence leftSig midSig leftSame =>
      cases right with
      | mk midSigObj' rightSigObj midEvidence' rightEvidence midSig' rightSig rightSame =>
          exact Exists.intro leftSigObj
            (Exists.intro rightSigObj
              (Exists.intro leftEvidence
                (Exists.intro rightEvidence
                  (And.intro leftSig
                    (And.intro rightSig
                      (eqv.trans leftSame (eqv.trans (det midSig midSig') rightSame)))))))

theorem GeneratedSameSig_psameBase
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist} {p q : s.Pkg}
    (gen : GeneratedSameSig s P h k)
    (left : s.TokIntro P gen.leftSigObj p)
    (right : s.TokIntro P gen.rightSigObj q) : PsameBase s P p q := by
  exact PsameBase.intro left right gen.sigSame

theorem PsameBase_to_GeneratedSameSig_under_tok_unique
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {h k : s.Hist} {x y : s.SigObj} {p q : s.Pkg}
    {leftEvidence rightEvidence : s.Evidence}
    (leftSig : s.SigGen P h x leftEvidence)
    (rightSig : s.SigGen P k y rightEvidence)
    (leftTok : s.TokIntro P x p)
    (rightTok : s.TokIntro P y q)
    (base : PsameBase s P p q) : Nonempty (GeneratedSameSig s P h k) := by
  exact Nonempty.intro {
    leftSigObj := x
    rightSigObj := y
    leftEvidence := leftEvidence
    rightEvidence := rightEvidence
    leftSig := leftSig
    rightSig := rightSig
    sigSame := PackageReflection_base eqv tok leftTok rightTok base
  }

theorem ClosureReflect_to_GeneratedSameSig
    {s : BaseReflectionSetup} {P : s.Pi}
    (reflect : ClosureReflect s P)
    {h k : s.Hist} {x y : s.SigObj} {p q : s.Pkg}
    {evL evR : s.Evidence}
    (leftSig : s.SigGen P h x evL)
    (rightSig : s.SigGen P k y evR)
    (leftTok : s.TokIntro P x p)
    (rightTok : s.TokIntro P y q)
    (closure : PsameEqClosure s P p q) :
    Nonempty (GeneratedSameSig s P h k) := by
  exact Nonempty.intro {
    leftSigObj := x
    rightSigObj := y
    leftEvidence := evL
    rightEvidence := evR
    leftSig := leftSig
    rightSig := rightSig
    sigSame := reflect leftTok rightTok closure
  }

end BEDC.BaseReflection

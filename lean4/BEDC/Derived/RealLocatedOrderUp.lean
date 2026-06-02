import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealLocatedOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RealLocatedOrderUp : Type where
  | mk (X Y R S D O A H C P N : BHist) :
      UnaryHistory N → hsame N X → RealLocatedOrderUp

def realLocatedOrderFields : RealLocatedOrderUp → List BHist
  | RealLocatedOrderUp.mk X Y R S D O A H C P N _ _ =>
      [X, Y, R, S, D, O, A, H, C, P, N]

theorem RealLocatedOrderCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (L : RealLocatedOrderUp)
    {X Y R S D O A H C P N xRead yRead windowRead toleranceRead apartnessRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realLocatedOrderFields L = [X, Y, R, S, D, O, A, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory Y →
          UnaryHistory R →
            UnaryHistory S →
              UnaryHistory D →
                UnaryHistory O →
                  UnaryHistory A →
                    UnaryHistory H →
                      UnaryHistory C →
                        Cont X R xRead →
                          Cont Y R yRead →
                            Cont R S windowRead →
                              Cont S D toleranceRead →
                                Cont O A apartnessRead →
                                  Cont H C replayRead →
                                    PkgSig bundle P pkg →
                                      SemanticNameCert
                                          (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row Y ∨ hsame row R ∨
                                              hsame row S ∨ hsame row D ∨ hsame row O ∨
                                                hsame row A ∨ Cont X R xRead ∨
                                                  Cont Y R yRead ∨ Cont R S windowRead ∨
                                                    Cont S D toleranceRead ∨
                                                      Cont O A apartnessRead ∨
                                                        Cont H C replayRead)
                                          (fun row : BHist =>
                                            PkgSig bundle P pkg ∧ hsame row N)
                                          hsame ∧
                                        UnaryHistory xRead ∧ UnaryHistory yRead ∧
                                          UnaryHistory windowRead ∧
                                            UnaryHistory toleranceRead ∧
                                              UnaryHistory apartnessRead ∧
                                                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro fieldsEq unaryX unaryY unaryR unaryS unaryD unaryO unaryA unaryH unaryC xCont
    yCont windowCont toleranceCont apartnessCont replayCont pkgP
  rcases L with
    ⟨x0, y0, r0, s0, d0, o0, a0, h0, c0, p0, n0, unaryn0, nameToSource0⟩
  cases fieldsEq
  have xUnary : UnaryHistory xRead :=
    unary_cont_closed unaryX unaryR xCont
  have yUnary : UnaryHistory yRead :=
    unary_cont_closed unaryY unaryR yCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryR unaryS windowCont
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryS unaryD toleranceCont
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed unaryO unaryA apartnessCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryH unaryC replayCont
  have sourceN :
          (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryn0⟩
  have cert :
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row Y ∨ hsame row R ∨ hsame row S ∨
                  hsame row D ∨ hsame row O ∨ hsame row A ∨ Cont X R xRead ∨
                    Cont Y R yRead ∨ Cont R S windowRead ∨
                      Cont S D toleranceRead ∨ Cont O A apartnessRead ∨
                        Cont H C replayRead)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row N)
              hsame := by
    exact {
      core := {
            carrier_inhabited := Exists.intro N sourceN
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
            exact Or.inl (hsame_trans source.left nameToSource0)
      ledger_sound := by
            intro _row source
            exact ⟨pkgP, source.left⟩
    }
  exact
    ⟨cert, xUnary, yUnary, windowUnary, toleranceUnary, apartnessUnary, replayUnary⟩

theorem RealLocatedOrderCarrier_apartness_handoff [AskSetup] [PackageSetup]
    (L : RealLocatedOrderUp)
    {X Y R S D O A H C P N xRead yRead windowRead toleranceRead locatedRead
      apartnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realLocatedOrderFields L = [X, Y, R, S, D, O, A, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory Y →
          UnaryHistory R →
            UnaryHistory S →
              UnaryHistory D →
                UnaryHistory O →
                  UnaryHistory A →
                    Cont X R xRead →
                      Cont Y R yRead →
                        Cont R S windowRead →
                          Cont S D toleranceRead →
                            Cont toleranceRead O locatedRead →
                              Cont locatedRead A apartnessRead →
                                PkgSig bundle P pkg →
                                  UnaryHistory xRead ∧ UnaryHistory yRead ∧
                                    UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                                      UnaryHistory locatedRead ∧
                                        UnaryHistory apartnessRead ∧
                                          Cont toleranceRead O locatedRead ∧
                                            Cont locatedRead A apartnessRead ∧
                                              PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro fieldsEq unaryX unaryY unaryR unaryS unaryD unaryO unaryA xCont yCont windowCont
    toleranceCont locatedCont apartnessCont pkgP
  rcases L with ⟨x0, y0, r0, s0, d0, o0, a0, h0, c0, p0, n0, _unaryN, _sameN⟩
  cases fieldsEq
  have xUnary : UnaryHistory xRead :=
    unary_cont_closed unaryX unaryR xCont
  have yUnary : UnaryHistory yRead :=
    unary_cont_closed unaryY unaryR yCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryR unaryS windowCont
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryS unaryD toleranceCont
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed toleranceUnary unaryO locatedCont
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed locatedUnary unaryA apartnessCont
  exact
    ⟨xUnary, yUnary, windowUnary, toleranceUnary, locatedUnary, apartnessUnary, locatedCont,
      apartnessCont, pkgP⟩

end BEDC.Derived.RealLocatedOrderUp

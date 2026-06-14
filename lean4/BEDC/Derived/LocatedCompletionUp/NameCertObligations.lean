import BEDC.Derived.LocatedCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (L : LocatedCompletionUp)
    {M S E W R D A H C P N sourceRead separatedRead embeddingRead windowRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    locatedCompletionFields L = [M, S, E, W, R, D, A, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory S ->
          UnaryHistory E ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory A ->
                    Cont M S sourceRead ->
                      Cont sourceRead E separatedRead ->
                        Cont separatedRead W embeddingRead ->
                          Cont embeddingRead R windowRead ->
                            Cont windowRead A realSeal ->
                              PkgSig bundle P pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M ∨ hsame row S ∨ hsame row E ∨
                                        hsame row W ∨ hsame row R ∨ hsame row D ∨
                                          hsame row A ∨ Cont M S sourceRead ∨
                                            Cont sourceRead E separatedRead ∨
                                              Cont separatedRead W embeddingRead ∨
                                                Cont embeddingRead R windowRead ∨
                                                  Cont windowRead A realSeal)
                                    (fun row : BHist =>
                                      PkgSig bundle P pkg ∧ hsame row realSeal)
                                    hsame ∧
                                  UnaryHistory sourceRead ∧ UnaryHistory separatedRead ∧
                                    UnaryHistory embeddingRead ∧ UnaryHistory windowRead ∧
                                      UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields metricUnary separatedUnary embeddingUnary windowUnary readbackUnary _dyadicUnary
    realUnary metricSeparated sourceEmbedding separatedWindow embeddingReadback windowReal
    provenancePkg
  cases L with
  | mk Lm Ls Le Lw Lr Ld La Lh Lc Lp Ln =>
      change [Lm, Ls, Le, Lw, Lr, Ld, La, Lh, Lc, Lp, Ln] =
        [M, S, E, W, R, D, A, H, C, P, N] at fields
      injection fields with metricEq fieldsTail
      injection fieldsTail with separatedEq fieldsTail
      injection fieldsTail with embeddingEq fieldsTail
      injection fieldsTail with windowEq fieldsTail
      injection fieldsTail with readbackEq fieldsTail
      injection fieldsTail with dyadicEq fieldsTail
      injection fieldsTail with realEq fieldsTail
      injection fieldsTail with _transportEq fieldsTail
      injection fieldsTail with _replayEq fieldsTail
      injection fieldsTail with provenanceEq _localEq
      cases metricEq
      cases separatedEq
      cases embeddingEq
      cases windowEq
      cases readbackEq
      cases dyadicEq
      cases realEq
      cases provenanceEq
      have sourceUnary : UnaryHistory sourceRead :=
        unary_cont_closed metricUnary separatedUnary metricSeparated
      have separatedReadUnary : UnaryHistory separatedRead :=
        unary_cont_closed sourceUnary embeddingUnary sourceEmbedding
      have embeddingReadUnary : UnaryHistory embeddingRead :=
        unary_cont_closed separatedReadUnary windowUnary separatedWindow
      have windowReadUnary : UnaryHistory windowRead :=
        unary_cont_closed embeddingReadUnary readbackUnary embeddingReadback
      have realSealUnary : UnaryHistory realSeal :=
        unary_cont_closed windowReadUnary realUnary windowReal
      have cert :
          SemanticNameCert
              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row S ∨ hsame row E ∨ hsame row W ∨
                  hsame row R ∨ hsame row D ∨ hsame row A ∨
                    Cont M S sourceRead ∨ Cont sourceRead E separatedRead ∨
                      Cont separatedRead W embeddingRead ∨ Cont embeddingRead R windowRead ∨
                        Cont windowRead A realSeal)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row realSeal)
              hsame := {
        core := {
          carrier_inhabited :=
            Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr windowReal))))))))))
        ledger_sound := by
          intro _row source
          exact ⟨provenancePkg, source.left⟩
      }
      exact
        ⟨cert, sourceUnary, separatedReadUnary, embeddingReadUnary, windowReadUnary,
          realSealUnary⟩

end BEDC.Derived.LocatedCompletionUp

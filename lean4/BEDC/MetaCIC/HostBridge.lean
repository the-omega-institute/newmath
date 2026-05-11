import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import Lean.Elab.Command
import Lean.Meta.Basic

namespace BEDC.MetaCIC.HostBridge

open Lean Meta Elab Command

def reprTerm : Term → Format
  | Term.var i => "Term.var " ++ repr i
  | Term.app f a => "Term.app " ++ reprTerm f ++ " " ++ reprTerm a
  | Term.lam dom body => "Term.lam " ++ reprTerm dom ++ " " ++ reprTerm body
  | Term.pi dom cod => "Term.pi " ++ reprTerm dom ++ " " ++ reprTerm cod
  | Term.sort => "Term.sort"

instance : Repr Term where
  reprPrec t _ := reprTerm t

/-- 把一个 host Lean `Expr` 尝试翻译成 `BEDC.MetaCIC.Term`。
    简化: 覆盖 sort、变量、应用、lambda、Pi。 -/
partial def reflectExpr (e : Expr) : MetaM (Option Term) := do
  match e with
  | Expr.sort _ =>
      return some Term.sort
  | Expr.bvar i =>
      return some (Term.var i)
  | Expr.app f a =>
      let fR? ← reflectExpr f
      let aR? ← reflectExpr a
      match fR?, aR? with
      | some fR, some aR => return some (Term.app fR aR)
      | _, _ => return none
  | Expr.lam _ dom body _ =>
      let domR? ← reflectExpr dom
      let bodyR? ← reflectExpr body
      match domR?, bodyR? with
      | some dom', some body' => return some (Term.lam dom' body')
      | _, _ => return none
  | Expr.forallE _ dom cod _ =>
      let domR? ← reflectExpr dom
      let codR? ← reflectExpr cod
      match domR?, codR? with
      | some dom', some cod' => return some (Term.pi dom' cod')
      | _, _ => return none
  | _ =>
      -- 未覆盖类型: const, mvar, mdata, proj, fvar, letE, lit
      return none

/-- Command 入口: `#reflect_metacic e` 打印 e 的 MetaCIC encoding (如能 encode). -/
elab "#reflect_metacic " e:term : command => do
  liftTermElabM do
    let expr ← Term.elabTerm e none
    let metaTerm? ← reflectExpr expr
    match metaTerm? with
    | some metaTerm => Lean.logInfo m!"MetaCIC encoding: {repr metaTerm}"
    | none => Lean.logInfo m!"cannot encode: {repr expr}"

end BEDC.MetaCIC.HostBridge

-- Sanity demo
section
  open BEDC.MetaCIC.HostBridge

  -- Should encode as Term.sort
  -- #reflect_metacic Sort 0
  -- Above may or may not work depending on universe handling
end

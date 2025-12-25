
# Tactics

## General Tactics

## `hord`

* `hord` tries `ord_trans` first
* if `ord_trans` fails, `hord` expands goal (`ord t _ _`) by `ord_exp0`, `ord_exp1`, or `ord_exp0` corresponding to the form of `t` and call `auto`
* We use `ord_expN` in order to control the expansion
  * If we simply evaluate `ord` instead, for example, the goal would be a huge term
* Since `hord` is assumed to be called by `hauto` explained later, it does not `unfold` functions or `mono`.

## `hsubst`

* takes a equation and tries to prove it using `omega`, then subst according to the equation.
* is used when goal contains some terms that are not well treated by Coq, such as `n - 0` or `S n - 1`

## Specialized Tactics

## `rd_fixpoint`

* unfold the correspondint fixpoint by `apply`ing `FPfixpoint` and `unfold`ing `fixpoint_gen`.
* is called from `hred`

## `hred`

* calculates the first function in a goal.
* When head function is
    * a normal function defined by `Definition`, call `red`
    * a fixpoint, call `rd_fixpoint`
    * a function literal (lambda), call `simpl`.
    * Then, call `simpl`.

## `hauto`

* repeatedly calls appropriate tactics according to a goal.
  * `/\` -> `split`
  * `\/` -> `(left; ... || right; ...)`
  * `ord ...` -> `hord`
  * `mono ...` -> `unfold mono; ...`
  * `n = m` -> `omega`
  * ...
* fails unless solve the focused goal
* can treat `\/` poorly


;Generate code for your input, output

;chez chez-lib.sc {self}.sc
;mychez {self}.sc
;(load "c:/path/to/chez-lib/lib.sc")

#|
= todo
  - 2 in 2 out
|#

;--

(def (null . paras)
  nil
)

(def (id-last . xs)
  (last xs)
)

;--

(def (form-f8 fs) ;faster and "best"
  (let-values
    ( [(f m g h  i j k l) (redu values fs)] )
    `(lam (x)
      (let ([X (,m (,f x))]) ;to simplify id id-last null ..
        (def (_ ret x)
          (if~
            (nilp (,h x))
              (,k (,j ret) (,i x))
            (_ (,l (car x) ret) (cdr x))
        ) )
        (_ (,g x) X)
) ) ) )
(def (f8 f  m g h i j  k l) ;"faster" and "best" ;asd3
  (lam (x)
    (let ([X (m (f x))])
      (def (~ ret x)
        (if~
          (nilp (h x))
            (k (j ret) (i x))
          (eql X x) ;@
            (k (j ret) (i x))
          (~ (l (car x) ret) (cdr x))
      ) )
      (def (_ ret x ini?)
        (if~
          (nilp (h x))
            (k (j ret) (i x))
          ini?
            (~ ret x) ;here, u may think of how to expand if-else at pos of else with ano fx glob func
          (_ (l (car x) ret) (cdr x) T)
      ) )
      (_ (g x) X F)
) ) )

(def (form-f7.2 fs) ;for list of 2 paras
  (form-f8 (cons (car fs) [cons 'rev (cdr fs)]))
)
(def (f7.2 f g h i j  k l) ;7 is good!
  (f8 f rev g h i j  k l)
)

;(code-for '(a b) '(b a))
(def/va
  (code-for in out [fx f7.2] [n-fns 7] [form-fx form-f7.2]
    ;null id-last id
    ;cons rev
    ;car cadr cdr last
    ;nilp atomp consp
    ;eq = eql
    ;0 1 1+
    ;`(car rev cadr nilp id-last id cons) ;cdr? null?
    [ops `(rev null  id id-last  nilp cdr cadr car cons)]
    [= eql] ) ;rev last
    ;[ops `(id id-last null  nilp cdr car cons)] ) ;(cons x)?
  (clean-choose)
  (reset-randseed)
  (letn
    ( (ops  (rand-seq ops))
      ;[ops     (rev ops)]
      [op-syms  ops] ;!
      [ops     (map ev  op-syms)] ;!
      [op-mapp (zip ops op-syms)]
      [show    (curry map (curry key->val op-mapp))]
      [fs   (chooses ops n-fns T)] ;!
      (main (redu fx fs)) ;!
      [resl (try (= out (main in)))] ;?
      [bool (if (try-fail? resl) F resl)] )
    (if bool
      (form-fx (show fs)) ;
      [fail] ;fail-and-goon
) ) )

;(load (str *lib-path* "demo/gen-code.sc"))

;(cost (code-for '(1 2) '2))     
;(cost (code-for '(1 2) '(2 1))) 
;(cost (code-for '([a s][d f]) '(a s d f) f7.2 7 form-f7.2))
;(cost (code-for '([a s][d f]) '(a s d f) f8 8 form-f8))
;(setq next2 [car (cost (code-for '([a s d f] s) 'd f7.2 7 form-f7.2))])

;if 2 rand resls of 2 cases are the same, we could nearly say, that is the answer

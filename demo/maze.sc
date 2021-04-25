
;Maze: make-maze, show-maze

;chez chez-lib.sc maze.sc
;mychez play-piano.sc
;(load "c:/path/to/chez-lib/lib.sc")

#|
= Update notes
  - add comments
|#

;-|+ o
;1110F
;#x0 #x1 ~ #xb #xF

;1*w
;;1 000...*(w-2) 1
;;1 01..*(w-1)/2
;;...*(h-3)/2
;;10001
;1*w

;11111
;10o01
;1o1o1
;10o01
;11111

;2: 1 0 o0..*(w-3)/2 1
;3: 1 o 1o..*n23 1
;(rand-0/1)

;demo
;todo [find ascii] [algo to solve maze] [rand-entry] [chk-entry] [new-algo]

;X~>Y
;1 o.  w
;1  .x w
;o,x <= (w-1)/2,(w+1)/2
(def/va (maze [w 20] [h 20]) ;[min 5] ;[cross '+] [row '-] [col '|]
  (letn
    ( [even->odd (lam (x) (if [even? x] (1+ x) x))]
      [w (even->odd w)]
      [h (even->odd h)]
      [wh (list w h)]
      [line1 (xn->list 1 w)]
    )
    ; line 2
    (def/va (line~2 [mark? F] [i-mark 4]) ;mark 'o/'x
      (def (~ xs i mark?)
        (if~
          (<= i 2)
            xs
          [<= i i-mark]
            [~
              (cons [rand-ab]
                (cons (if mark? 'X 0) ;
                  xs ) )
              (- i 2)
              F ] ;            
          [~ (cons [rand-ab] (cons 0 xs)) (- i 2) mark?] ;
      ) )
      (cons 1 (cons 0 ;
          [~ (list 1) (1- w) mark?] ;
    ) ) )
    ; line 3
    (def/va (line~3 [cross 1] [bar 1])
      (def (~ xs i)
        (if (<= i 2) xs
          [~ (cons cross (cons [rand-ab 0 bar] xs)) (- i 2)] ;
      ) )
      (cons 1 (cons [rand-ab 0 bar]
          [~ (list 1) (1- w)]
    ) ) )
    ; check
    (def (chk) [redu logic-and (map (rcurry >= 5) wh)])
    ; rand
    (def/va (rand-ab [a 0] [b 1])
      (if [= 1 (ceil (random 3.59375))] b a) ) ;(2,4) ~> 3 ;(avg 3.5625 3.625)
    ; main func
    (def (~ xs i)
      (if (>= i h) xs
        [~ (cons [line~2] (cons [line~3 ] xs)) (+ i 2)]
    ) )
    ; reset
    [reset-randseed]
    ;-- main
    (if (chk)    
      (cons line1
        (cons [line~2 T (half (1- w))]
          (cons [line~3 ]
            [~ (list [line~2 T (half (+ w 3))] line1) (+ 2 1 2)] ;
      ) ) )
      nil
) ) )

;o x
;man,d ~> flag,e; trace,f
;(map str '(#\x26DA #\x274E))
(def/va (show-maze maz [mrks `((0 1 X) ,[map str '(" " "E" "o")])] [sep ""])
  (letn
    ( [mrks (map (curry map list) mrks)]
      [f (rcurry (curry redu replaces) mrks)]
      [tmp (map [flow f (rcurry strcat/sep sep)] maz)]
    )
    (echol [strcat/sep tmp "\n"])
) )

;-- main

;(setq mz (maze 20 20))
;(show-maze mz)

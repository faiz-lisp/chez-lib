
;Maze: make-maze, show-maze

;chez chez-lib.sc maze.sc
;mychez play-piano.sc
;(load "c:/path/to/chez-lib/lib.sc")

#|
= Update notes
  - upd
  - add wall, blank
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
(def/va (maze [w 20] [h 20] [wall 0] [blank 1]) ;[min 5] ;[cross '+] [row '-] [col '|] 
  (letn
    ( [even->odd (lam (x) (if [even? x] (1+ x) x))]
      [w (even->odd w)]
      [h (even->odd h)]
      [wh (list w h)]
      [line1 (xn->list wall w)]
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
                (cons (if mark? 'X blank) ;
                  xs ) )
              (- i 2)
              F ] ;            
          [~ (cons [rand-ab] (cons blank xs)) (- i 2) mark?] ;
      ) )
      (cons wall (cons blank ;
          [~ (list wall) (1- w) mark?] ;
    ) ) )
    ; line 3
    (def/va (line~3 [cross wall] [bar wall])
      (def (~ xs i)
        (if (<= i 2) xs
          [~ (cons cross (cons [rand-ab blank bar] xs)) (- i 2)] ;
      ) )
      (cons wall (cons [rand-ab blank bar]
          [~ (list wall) (1- w)]
    ) ) )
    ; check
    (def (chk) [redu logic-and (map (rcurry >= 5) wh)])
    ; rand
    (def/va (rand-ab [a blank] [b wall]) ;1 0
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

;0
;c 1~9 a b
;. - | L closewise... T cw... +
;closewise: 0000 UpRtDnLf
;0 0101 1010 1100 0110 0011 1001 0111 1011 1101 1110 1111
;(setq a '(0 5 #xA #xC 6 3 9 7 #xB #xD #xE #xF))
;(setq b '(|.| - I L t L3 J T T2 T3 T4 +))
;(0 3 5 6 7 9 10 11 12 13 14 15)
;(|.| L3 - t T J I T2 L T3 T4 +)
;rest 1 2 4 8

;o x
;man,d ~> flag,e; trace,f
;(map str '(#\x26DA #\x274E))
(def/va (show-maze mz [sep ""] [mrks `((0 1 X) ,[map str '(" " "E" "o")])])
  (letn
    ( [mrks (map (curry map list) mrks)]
      [f (rcurry (curry redu replaces) mrks)]
      [tmp (map [flow f (rcurry strcat/sep sep)] mz)]
    )
    (echol [strcat/sep tmp "\n"])
) )

;(get-pt-cross mz '(3 3)) ;[start 0]
(def/va (get-pt-cross xs pt [cw? T]) ;[start 0]
  ;,y-1 x+1, ,y+1 x-1,
  (letn
    ( [pt.x (car pt)] [pt.y (cadr pt)]
      [pt0 (list pt.x (1- pt.y))]
      [pt1 (list (1+ pt.x) pt.y)]
      [pt2 (list pt.x (1+ pt.y))]
      [pt3 (list (1- pt.x) pt.y)] )    
    (pts->vals xs (list pt0 pt1 pt2 pt3))
) )

;-- main

;(setq mz (maze 20 20))
;(show-maze mz)

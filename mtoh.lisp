; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
; Function to create a list describing
; a move made from peg 'x' to 'y'
(defun move (x y)
  (declare (xargs :guard t))
  (list 'move 'from 'peg x 'to 'peg y))

#|
NOTE: The 'start', 'inter', and 'dest' inputs for the following functions
      act as tags for each of the three pegs, with the 'start' and 'dest' tagged pegs
      indicating from where and to where we are moving the n amount of disks.
|#

(set-termination-method :measure)
(set-well-founded-relation n<)
(set-defunc-typed-undef nil)
(set-defunc-generalize-contract-thm nil)
(set-gag-mode nil)

#|
Looking at the recursive formula of solver, we create a measure function
solver-moves which mimics solver in form, and instead of appending the outputs,
adds the number of calls to move.
     pattern - boolean flag to indicate which pattern is being used
     start   - tag for the starting peg
     inter   - tag for the intermediate peg
     dest    - tag for the destination peg
     n       - number of total disk that all begin
               stacked on the starting peg
|#
(defun solver-moves (pattern start inter dest n)
  (declare (irrelevant start inter dest))
  (if (zp n)
    0
    (if pattern 
      (+ (solver-moves pattern start dest inter (1- n))
         1
         (solver-moves (not pattern) inter dest start (1- n))
         (solver-moves pattern start inter dest (1- n)))
      (+ (solver-moves pattern start inter dest (1- n))
         (solver-moves (not pattern) dest start inter (1- n))
         1
         (solver-moves pattern inter start dest (1- n))))))

#|
For our solver, when (equal pattern t) refers to the North-South-South Pattern
and the (equal pattern nil) refers to the North-North-South Pattern.
     pattern - boolean flag to indicate which pattern is being used
     start - tag for the starting peg
     inter - tag for the intermediate peg
     dest  - tag for the destination peg
     n     - number of total disk that all begin
             stacked on the starting peg
|#

(defun solver (pattern start inter dest n)
  (declare (xargs :measure (solver-moves pattern start inter dest n)
                  :guard (natp n)))
  (if (zp n)
    nil
    (if pattern 
      (append (solver pattern start dest inter (1- n)) 
              (cons (move start dest) 
                    (append (solver (not pattern) inter dest start (1- n)) 
                            (solver pattern start inter dest (1- n)))))
      (append (solver pattern start inter dest (1- n)) 
              (append (solver (not pattern) dest start inter (1- n))
                      (cons (move start dest)
                            (solver pattern inter start dest (1- n))))))))

#|
Main function to solve a MToH puzzle
   start - tag for the starting peg
   inter - tag for the intermediate peg
   dest  - tag for the destination peg
   n     - number of total disks that all begin 
           stacked on the starting peg
|#
(defun mtoh (start inter dest n)
  (if (zp n)
    nil
    (solver t start inter dest n)))

#|
Number of moves for n amount of disks:

1 disk : 1 : 3^0

2 disks : 4 : 3^1 + 1

3 disks : 13 : 3^2 + 3^1 + 3^0

4 disks : 40 : 3^3 + 3^2 + 3^1 + 3^0

5 disks : 121 : 3^4 + 3^3 + 3^2 + 3^1 + 3^0

n disks : (3^n - 1)/2
|#


; Proves that starting at either pattern will result in the same number of moves
; alo proves that there is no difference in the number of moves whether you
; use the NSS or NNS pattern.
(defthm solver-moves-equal
  (implies (natp n)
           (equal (solver-moves t 'a 'a 'a n)
                  (solver-moves nil 'a 'a 'a n))))

; Proves that our solver-moves method returns (3^n - 1) / 2 moves for n starting disks
(defthm num-moves-solver
  (implies (natp n)
           (equal (solver-moves t 'a 'a 'a n)
                  (/ (1- (expt 3 n)) 2))))#|ACL2s-ToDo-Line|#



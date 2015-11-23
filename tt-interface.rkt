#lang racket
(require racket/class)
(require racket/gui/base)

(require "tt-macros.rkt")
(require "tt.rkt")

;;; A widget to display a single proof goal, formatted nicely
(define (print-sequent sequent)
  (let ((Γ (⊢-context sequent))
        (T (⊢-goal sequent)))
    (define (display-context context)
      (if (null? context)
          "·"
          (string-join (map (lambda (element)
                              (format "~a:~a"
                                      (car element)
                                      (cadr element)))
                            (reverse context))
                       ", ")))
    (format "~a ⊢ ~a" (display-context Γ) T)))


(define proof-goal-view%
  (class object%
    (init goal parent)
    (super-new)

    (define widget
      (new message%
           [parent parent]
           [stretchable-height #f]
           [stretchable-width #f]
           [label (print-sequent goal)]))))


(define proof-goal-editor-panel%
  (class vertical-panel%

    (init-field parent goal proof-parent)

    (field (extractor #f)
           (status 'unrefined)) ;; can be unrefined, refined, error

    (super-new [parent parent] [alignment '(left top)] [stretchable-height #f])

    (define (status-indicator)
      (match status
        ['unrefined "—"]
        ['refined "➘"]
        ['error "✘"]))


    (define inner-pane (new horizontal-panel%
                             [parent this]
                             [alignment '(left top)]))
    (define status-view (new message%
                             [parent inner-pane]
                             [label (status-indicator)]))
    (define goal-view (new proof-goal-view% [parent inner-pane]
                           [goal goal]))

    (define child-widget #f)

    (define/public (complete?)
      (and (equal? status 'refined)
           (for/and ([child-editor
                      (if (is-a? child-widget subgoals-panel%)
                          (send child-widget get-subgoal-editors)
                          empty)])
             (send child-editor complete?))))

    (define/public (update-status-view)
      (when proof-parent
        (send proof-parent update-status-view))
      (send status-view set-label
            (if (complete?) "✔" (status-indicator))))

    (define (delete-child-widget)
      (when child-widget
        (send this delete-child child-widget))
      (set! child-widget #f))

    (define (replace-child-widget new-widget)
      (delete-child-widget)
      (set! child-widget new-widget))

    (define (show-error exn)
      (set-field! status this 'error)
      (update-status-view)
      (replace-child-widget
       (new text-field%
            [parent this]
            [label #f]
            [init-value (format "Error refining:\n~a" exn)]
            [style '(multiple)]
            [enabled #f])))

    (define (read-current-input)
      (read (open-input-string (send tactic-entry get-value))))

    (define (refine button event)
      (with-handlers ([exn:fail? show-error])
        (let* ((parsed (read-current-input))
               (refine (eval `(,parsed ,goal)))
               (subgoals (refinement-new-goals refine))
               (extract (refinement-extract refine)))
         (set-field! extractor this extract)
         (set-field! status this 'refined)
         (send tactic-entry enable #f)
         (send undo-refine-button enable #t)
         (send refine-button enable #f)
         (replace-child-widget
          (new subgoals-panel%
               [parent this]
               [subgoals subgoals]))
         (update-status-view))))

    (define (undo-refine button event)
      (set-field! extractor this #f)
      (set-field! status this 'unrefined)
      (send tactic-entry enable #t)
      (send undo-refine-button enable #f)
      (send refine-button enable #t)

      (delete-child-widget)
      (update-status-view))

    (define tactic-entry
      (new text-field% [parent inner-pane]
           [label "Rule"]
           [callback (lambda (widget event)
                       (when (equal? (send event get-event-type)
                                     'text-field-enter)
                         (refine widget event)))]))

    (define refine-button
      (new button%
           [parent inner-pane]
           [label "Refine"]
           [callback refine]))

    (define undo-refine-button
      (new button%
           [parent inner-pane]
           [label "Undo"]
           [callback undo-refine]
           [enabled #f]))

    (define (get-proof-step)
      (match (get-field status this)
        [(or 'unrefined 'error)
         (proof-goal goal)]
        ['refined
         (proof-step goal
                     (read-current-input)
                     (if (is-a? child-widget subgoals-panel%)
                         (send child-widget subgoal-proof-steps)
                         empty))]))
    (public get-proof-step)))


(define subgoals-panel%
  (class horizontal-panel%
    (init subgoals parent)
    (super-new [parent parent]
               [alignment '(left top)]
               [stretchable-height #f])

    (define spacer (new panel%
                        [parent this]
                        [min-width 30]
                        [stretchable-width #f]))
    (define inner-panel (new vertical-panel%
                            [parent this]
                            [alignment '(left top)]))

    (define subgoal-editors
      (for/list ([goal subgoals])
       (new proof-goal-editor-panel%
            [parent inner-panel]
            [proof-parent parent]
            [goal goal])))
    (define/public (get-subgoal-editors) subgoal-editors)

    (define (subgoal-proof-steps)
      (for/list ([goal-editor subgoal-editors])
        (send goal-editor get-proof-step)))
    (public subgoal-proof-steps)))


(define (export-proof proof)
  (define frame (new frame%
                     [label "Proof"]
                     [width 600]
                     [height 600]
                     [alignment '(left top)]))

  (define proof-text
    (let ((port (open-output-string)))
      (pretty-write proof port)
      (get-output-string port)))

  (new text-field%
       [parent frame]
       [style '(multiple)]
       [label #f]
       [init-value proof-text])
  (send frame show #t))


(define (extract proof)
  (let ((port (open-output-string)))
    (with-handlers ([exn:fail?
                     (lambda (exn)
                       (displayln "An error occurred while checking the proof:" port)
                       (displayln exn port))])
      (match (check-proof proof)
        [(proof-done extracted)
         (displayln "Proof complete. Extracted term:" port)
         (pretty-write extracted port)]
        [(proof-incomplete remaining)
         (displayln "Proof incomplete. Unsolved goals:" port)
         (for ([goal remaining])
           (display " * " port)
           (displayln (print-sequent goal) port))]))
    (define frame (new frame%
                       [label "Proof"]
                       [width 600]
                       [height 600]
                       [alignment '(left top)]))
    (new text-field%
       [parent frame]
       [style '(multiple)]
       [label #f]
       [init-value (get-output-string port)])
    (send frame show #t)))


(define (prove thm)
  (define frame (new frame%
                     [label "Proof Editor"]
                     [width 800]
                     [height 600]
                     [alignment '(left top)]))

  (define mb (new menu-bar% [parent frame]))

  (define m-file (new menu% [label "Proof"] [parent mb]))

  (define m-edit (new menu% [label "Edit"] [parent mb]))
  (append-editor-operation-menu-items m-edit #f)

  (define initial-goal (new proof-goal-editor-panel%
                            [parent frame]
                            [goal thm]
                            [proof-parent #f]))

  (new menu-item%
       [label "Export"]
       [parent m-file]
       [callback (lambda (x y) (export-proof (send initial-goal get-proof-step)))])
  (new menu-item%
       [label "Extract"]
       [parent m-file]
       [callback (lambda (x y) (extract (send initial-goal get-proof-step)))])

 
  (send frame show #t))



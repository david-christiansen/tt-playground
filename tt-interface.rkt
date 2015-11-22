#lang racket
(require racket/class)
(require racket/gui/base)

(require "tt-macros.rkt")
(require "tt.rkt")

;;; A widget to display a single proof goal, formatted nicely
(define proof-goal-view%
  (class object%
    (init goal parent)
    (super-new)
    (define Γ (⊢-context goal))
    (define T (⊢-goal goal))

    (define (display-context context)
      (if (null? context)
          "·"
          (string-join (map (lambda (element)
                              (format "~a:~a"
                                      (car element)
                                      (cadr element)))
                            (reverse context))
                       ", ")))
    (define widget
      (new message%
           [parent parent]
           [stretchable-height #f]
           [stretchable-width #f]
           [label (format "~a ⊢ ~a" (display-context Γ) T)]))))

(define proof-goal-editor-panel%
  (class vertical-panel%

    (init goal parent)

    (field (extractor #f)
           (status 'unrefined)) ;; can be unrefined, refined, error, complete

    (super-new [parent parent] [alignment '(left top)] [stretchable-height #f])

    (define (status-indicator)
      (match status
        ['unrefined "—"]
        ['refined "➘"]
        ['error "✘"]
        ['complete "✔"]))


    (define inner-pane (new horizontal-panel%
                             [parent this]
                             [alignment '(left top)]))
    (define status-view (new message%
                             [parent inner-pane]
                             [label (status-indicator)]))
    (define goal-view (new proof-goal-view% [parent inner-pane]
                           [goal goal]))
    

    (define child-widget #f)

    (define (update-status-view)
      (send status-view set-label (status-indicator)))

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

    (define (refine button event)
      (with-handlers ([exn:fail? show-error])
        (let* ((input (send tactic-entry get-value))
              (parsed (read (open-input-string input)))
              (refine (eval `(,parsed ,goal)))
              (subgoals (refinement-new-goals refine))
              (extract (refinement-extract refine)))
         (set-field! extractor this extract)
         (set-field! status this (if (null? subgoals) 'complete 'refined))
         (send tactic-entry enable #f)
         (send undo-refine-button enable #t)
         (send refine-button enable #f)
         (replace-child-widget
          (new proof-step-panel%
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
           [enabled #f]))))

(define proof-step-panel%
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
    (for ([goal subgoals])
      (new proof-goal-editor-panel%
           [parent inner-panel]
           [goal goal]))))


(define (prove thm)
  (define goals (list thm))

  (define frame (new frame%
                     [label "TT Interactions"]
                     [width 800]
                     [height 600]
                     [alignment '(left top)]))

  (define mb (new menu-bar% [parent frame]))
  (define m-edit (new menu% [label "Edit"] [parent mb]))
  (append-editor-operation-menu-items m-edit #f)

  (define initial-goal (new proof-goal-editor-panel% [parent frame] [goal thm]))
 
  (send frame show #t))



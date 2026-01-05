module Task.Script.Renderer where

import Preload

import Concur as Concur
import Concur.Dom (Widget)
import Concur.Dom.Attr as Attr
import Concur.Dom.Icon as Icon
import Concur.Dom.Input (Action(..))
import Concur.Dom.Input as Input
import Concur.Dom.Style (Kind(..), Position(..), Size(..), Stroke(..), Style(..))
import Concur.Dom.Style as Style
import Concur.Dom.Text as Text

import Data.Array as Array
import Data.Either.Nested as Either
import Data.HashMap as HashMap

import Task.Script.Annotation (Annotated(..), Checked, Status(..), unannotate, extractContext)
import Task.Script.Builder as Builder
import Task.Script.Context (Context, Typtext, aliases)
import Task.Script.Label (Label, Labeled, Name)
import Task.Script.Loader (validate)
import Task.Script.Syntax (Arguments(..), Branches, Constant(..), Expression(..), LabeledBranches, Match(..), Task(..))
import Task.Script.Type (BasicType, isFunction, isReference, isTask)
import Task.Script.World (World, Parameters)

---- Rendering -----------------------------------------------------------------

type Renderer = Checked Task -> Widget (Checked Task)
type RemovedRenderer = Checked Task -> Widget (IsRemoved * DidMoveOptions * Checked Task)

main :: World -> Name -> Widget (Name * Parameters * Checked Task)
main { types: s, context: g, tasks: ts } n =
  case HashMap.lookup n ts of
    Just (ps ~ t) -> Concur.repeat (n ~ ps ~ t) \(n' ~ ps' ~ t') ->
      let
        g' = HashMap.union ps g
        t'' = validate s g' t'
      in
        Style.column
          [ renderStart n' ps' >-> Either.in1
          , renderTask g' s t'' >-> Either.in2
          , renderStop
          , Text.head " "
          , Text.head "Code"
          , Text.code "TopHat" (show (unannotate t''))
          , Text.head "Tips"
          , renderTips
          , Text.head "Notes"
          , renderNotes
          ]
          >-> fix2 (n' ~ ps') t''
          >-> assoc
    Nothing -> Text.text <| "Could not find task " ++ quote n

renderTips :: forall a. Widget a
renderTips = Text.bullets
  [ Text.item <| Text.text "Hover over"
  , Text.bullets
      [ Text.item <| Text.text "arrows to see values in context"
      , Text.item <| Text.text "arguments to add or remove some"
      ]
  , Text.item <| Text.text "Click on"
  , Text.bullets
      [ Text.item <| Text.text "arrows to switch between internal/external step"
      , Text.item <| Text.text "bars to switch between and/or parallel"
      ]
  , Text.item <| Text.text "Double click on"
  , Text.bullets
      [ Text.item <| Text.text "arrows to add a new hole"
      , Text.item <| Text.text "bars to add a new branch"
      ]
  ]

renderNotes :: forall a. Widget a
renderNotes = Text.text "Editing matches (results) and expressions is currently not supported, as is adding fresh tasks to the library."

fixgo :: Widget (IsRemoved * DidMoveOptions * Checked Task) -> Widget (Checked Task)
fixgo g = do
  ( _ ~  _ ~ t) <- g 
  done <| t
-- TODO: case distinciton ?

renderTask :: Context -> Typtext -> Renderer
renderTask g s t = Style.column
  [ fixgo <| go t
  ]
  where
  go :: Checked Task -> Widget (IsRemoved * DidMoveOptions * Checked Task)
  go (Annotated a_t t) = case t of
    ---- Steps
    -- NOTE:
    -- Be aware of the INVARIANT: Branch and Select need to be inside a Step.
    
    -- m:                           match, aka params next to line
    -- t1:                          task before the step
    -- t2/(some task definition):   task after the step

    -- for task types, see Syntax.purs


    -- case following subtask::unguarded Branch of Lift. This is the end step of choose/pair combinators or final of functions
    Step m t1 orig@(Annotated a_b (Branch [ Constant (B true) ~ Annotated a_l (Lift e) ])) -> do
      c' ~ m' ~ (isremoved1' ~ didmove1' ~ t1') <- renderEnd go a_t m t1
      done <| case isremoved1' of
        Removed -> NotRemoved ~ defaultDidMove ~ (Annotated a_l (Lift e) )
        NotRemoved -> NotRemoved ~ defaultDidMove ~ (Annotated a_t <| Step m' t1' <| case c' of
          New -> Builder.new orig
          _ -> orig)

    -- case following subtask::unguarded Branch of other
    Step m t1 orig@(Annotated a_b (Branch [ Constant (B true) ~ t2 ])) -> do
      (isguarded' ~ e' ~ (didmove1' ~ c' ~ m')) ~ (isremoved1' ~ _ ~ t1') ~ (isremoved2' ~ didmove2' ~ t2') <- renderSingleUnguarded go a_t Hurry m t1 t2      
      done <| NotRemoved ~ case isremoved1' of
        Removed -> defaultDidMove ~ t2'
        NotRemoved -> case (didmove1' ~ t2') of
          ((MovedUp ~ NotMovedDown) ~ _) -> (MovedUp ~ NotMovedDown) ~ (Annotated a_t t)
          ((NotMovedUp ~ MovedDown) ~ (Annotated a_c (Step m2' t3' t4'))) -> defaultDidMove ~ (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Branch [Constant (B true) ~ Annotated a_c (Step m' t1' t4')] )
          --((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button press"
          _ -> defaultDidMove ~ case (didmove2' ~ t2') of
            ((MovedUp ~ NotMovedDown)) ~ (Annotated a_c (Step m2' t3' t4')) -> (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Branch [Constant (B true) ~ Annotated a_c (Step m' t1' t4')] )
            ((MovedUp ~ NotMovedDown) ~ _) -> panic "invalid move button press"
            ((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button case"
            _ -> Annotated a_t (Step m' t1' <| case(c' ~ isguarded') of
              (Hurry ~ Guarded) -> Annotated a_b <| Branch [ Constant (B false) ~ t2' ]
              (Hurry ~ NotGuarded) -> Annotated a_b <| Branch [ Constant (B true) ~ t2' ]
              (Delay ~ Guarded) -> Annotated a_b <| Select [ "Continue" ~ Constant (B false) ~ t2' ]
              (Delay ~ NotGuarded) -> Annotated a_b <| Select [ "Continue" ~ Constant (B true) ~ t2' ]
              (New ~ _) -> Builder.new orig)

    -- case following subtask::guarded Branch with 1 branch
    Step m t1 orig@(Annotated a_b (Branch [ e ~ t2 ])) -> do
      isdoubled' ~ (isguarded' ~ e' ~ (didmove1' ~ c' ~ m')) ~ (isremoved1' ~ _ ~ t1') ~ (isremoved2' ~ didmove2' ~ t2') <- renderSingleBranch go a_t m t1 (e ~ t2)       
      done <| NotRemoved ~ case isdoubled' of 
        Doubled -> defaultDidMove ~ (Annotated a_t <| Step m' t1' <| Annotated a_b <| Branch([e' ~ t2', Builder.always ~ Builder.item ]))
        NotDoubled -> case isremoved1' of
          Removed -> defaultDidMove ~ t2'
          NotRemoved -> case (didmove1' ~ t2') of
            ((MovedUp ~ NotMovedDown) ~ _) -> (MovedUp ~ NotMovedDown) ~ (Annotated a_t t)
            ((NotMovedUp ~ MovedDown) ~ (Annotated a_c (Step m2' t3' t4'))) -> defaultDidMove ~ (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Branch [e ~ Annotated a_c (Step m' t1' t4')] )
            --((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button press"
            _ -> defaultDidMove ~ case (didmove2' ~ t2') of
              ((MovedUp ~ NotMovedDown)) ~ (Annotated a_c (Step m2' t3' t4')) -> (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Branch [e ~ Annotated a_c (Step m' t1' t4')] )
              ((MovedUp ~ NotMovedDown) ~ _) -> panic "invalid move button press"
              ((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button case"
              _ -> Annotated a_t (Step m' t1' <| case (c' ~ isguarded') of
                (Hurry ~ Guarded) -> Annotated a_b <| Branch [e' ~ t2']
                (Hurry ~ NotGuarded) -> Annotated a_b <| Branch [ Constant (B true) ~ t2' ]
                (Delay ~ Guarded) -> Annotated a_b <| Select ["Continue" ~ e' ~ t2']
                (Delay ~ NotGuarded)-> Annotated a_b <| Select ["Continue" ~ Constant (B true) ~ t2' ]
                (New ~ _) -> Builder.new orig)

    -- case following subtask::guarded Branch with more than 1 branch
    Step m t1 orig@(Annotated a_b (Branch bs)) -> do
      (didmove1' ~ c' ~ m') ~ (isremoved1' ~ _ ~ t1') ~ bs' <- renderBranches go a_t m t1 bs
      done <| case isremoved1' of
        Removed -> Removed ~ defaultDidMove ~ (subtask a_b c' bs')
        NotRemoved -> case didmove1' of 
          (MovedUp ~ NotMovedDown) -> NotRemoved ~ (MovedUp ~ NotMovedDown) ~ (Annotated a_t t) 
          --(NotMovedUp ~ MovedDown) -> do nothing, just ignore
          _ -> NotRemoved ~ defaultDidMove ~ (Annotated a_t <| Step m' t1' <| subtask a_b c' bs')
      where
      subtask a_b c' bs' = case c' of
        Hurry -> Annotated a_b <| Branch bs'
        Delay -> Annotated a_b <| Select (addLabels bs')
        New -> Builder.new orig

    -- case following subtask::unguarded Select
    Step m t1 orig@(Annotated a_b (Select [ "Continue" ~ Constant (B true) ~ t2 ])) -> do
      (isguarded' ~ e' ~ (didmove1' ~ c' ~ m')) ~ (isremoved1' ~ _ ~ t1') ~ (isremoved2' ~ didmove2' ~ t2') <- renderSingleUnguarded go a_t Delay m t1 t2
      done <| NotRemoved ~ case isremoved1' of
        Removed -> defaultDidMove ~ t2'
        NotRemoved -> case (didmove1' ~ t2') of
          ((MovedUp ~ NotMovedDown) ~ _) -> (MovedUp ~ NotMovedDown) ~ (Annotated a_t t)
          ((NotMovedUp ~ MovedDown) ~ (Annotated a_c (Step m2' t3' t4'))) -> defaultDidMove ~ (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Select ["Continue" ~ Constant (B true) ~ Annotated a_c (Step m' t1' t4')] )
          --((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button press"
          _ -> defaultDidMove ~ case (didmove2' ~ t2') of
            ((MovedUp ~ NotMovedDown)) ~ (Annotated a_c (Step m2' t3' t4')) -> (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Select ["Continue" ~ Constant (B true) ~ Annotated a_c (Step m' t1' t4')] )
            ((MovedUp ~ NotMovedDown) ~ _) -> panic "invalid move button press"
            ((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button case"
            _ -> Annotated a_t (Step m' t1' <| case (c' ~ isguarded') of
              (Hurry ~ Guarded) -> Annotated a_b <| Branch [ Constant (B false) ~ t2' ]
              (Hurry ~ NotGuarded) -> Annotated a_b <| Branch [ Constant (B true) ~ t2' ]
              (Delay ~ Guarded) -> Annotated a_b <| Select [ "Continue" ~ Constant (B false) ~ t2' ]
              (Delay ~ NotGuarded) -> Annotated a_b <| Select [ "Continue" ~ Constant (B true) ~ t2' ]
              (New ~ _) -> Builder.new orig)

    --case following subtask::guarded Select with 1 branch
    Step m t1 orig@(Annotated a_b (Select [l ~ e ~ t2])) -> do
      isdoubled' ~ (isguarded' ~ (l' ~ e') ~ (didmove1' ~ c' ~ m')) ~ (isremoved1' ~ _ ~ t1') ~ (isremoved2' ~ didmove2' ~ t2') <- renderSingleSelect go a_t m t1 (l ~ e ~ t2)
      done <| NotRemoved ~ case isdoubled' of
        Doubled -> defaultDidMove ~ (Annotated a_t <| Step m' t1' <| Annotated a_b <| Select([l' ~ e' ~ t2', "Continue" ~ Builder.always ~ Builder.item ]))
        NotDoubled -> case isremoved1' of
          Removed -> defaultDidMove ~ t2'
          NotRemoved -> case (didmove1' ~ t2') of
            ((MovedUp ~ NotMovedDown) ~ _) -> (MovedUp ~ NotMovedDown) ~ (Annotated a_t t)
            ((NotMovedUp ~ MovedDown) ~ (Annotated a_c (Step m2' t3' t4'))) -> defaultDidMove ~ (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Select [l ~ e ~ Annotated a_c (Step m' t1' t4')] )
            --((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button press"
            _ -> defaultDidMove ~ case (didmove2' ~ t2') of
              ((MovedUp ~ NotMovedDown)) ~ (Annotated a_c (Step m2' t3' t4')) -> (Annotated a_t <| Step m2' t3' <| Annotated a_b <| Select [l ~ e ~ Annotated a_c (Step m' t1' t4')] )
              ((MovedUp ~ NotMovedDown) ~ _) -> panic "invalid move button press"
              ((NotMovedUp ~ MovedDown) ~ _) -> panic "invalid move button case"
              _ -> Annotated a_t (Step m' t1' <| case (c' ~ isguarded') of
                (Hurry ~ Guarded) -> Annotated a_b <| Branch ([e' ~ t2'])
                (Hurry ~ NotGuarded) -> Annotated a_b <| Branch ([Constant (B true) ~ t2' ])
                (Delay ~ Guarded) -> Annotated a_b <| Select [l' ~ e' ~ t2']
                (Delay ~ NotGuarded) -> Annotated a_b <| Select [l' ~ Constant (B true) ~ t2' ]
                (New ~ _) -> Builder.new orig)
                
    --case following subtask::guarded Select with more than 1 branch
    Step m t1 orig@(Annotated a_b (Select bs)) -> do
      (didmove1' ~ c' ~ m') ~ (isremoved1' ~ _ ~ t1') ~ bs' <- renderSelects go a_t m t1 bs
      done <| case isremoved1' of
        Removed -> Removed ~ defaultDidMove ~ (subtask a_b c' bs')
        NotRemoved -> case didmove1' of
          (MovedUp ~ NotMovedDown) -> NotRemoved ~ (MovedUp ~ NotMovedDown) ~ (Annotated a_t t)
          --(NotMovedUp ~ MovedDown) -> do nothing, just ignore
          _ -> NotRemoved ~ defaultDidMove ~ (Annotated a_t <| Step m' t1' <| subtask a_b c' bs')
      where 
      subtask a_b c' bs' = case c' of
        Hurry -> Annotated a_b <| Branch (removeLabels bs')
        Delay -> Annotated a_b <| Select bs'
        New -> Builder.new orig

    Step _ _ _ -> panic "invalid single step"
    -- m' ~ t1' ~ t2' <- renderSingle Hurry go m t1 t2
    -- done <| Annotated a_t (Step m' t1' t2')
    Branch _ -> panic "invalid single branch"
    Select _ -> panic "invalid single select"
    -- Branch bs -> do
    --   ts' <- renderContinuation Closed style_branch go (map snd bs)
    --   let bs' = Array.zip (map fst bs) ts'
    --   done <| Annotated ?h (Branch bs')
    -- Select bs -> do
    --   ts' <- renderContinuation Open style_branch go (map trd bs)
    --   let bs' = Array.zip (map fst2 bs) ts' |> map assoc
    --   done <| Annotated ?h (Select bs')
    --   where
    --   fst2 (x ~ y ~ _) = x ~ y
    --   assoc ((x ~ y) ~ z) = x ~ (y ~ z)

    ---- Editors
    Enter n -> do
      n' ~ o <- renderWithOptions n NotForked (renderEnter s n)
      done <| case getSecondUserOption o of 
        Forked -> (getFirstUserOption o) ~ defaultDidMove ~ renderNewFork (Annotated a_t t) (Enter n')
        NotForked -> (getFirstUserOption o) ~ defaultDidMove ~ (Annotated a_t <| Enter n')
   
    Update e -> do
      e' ~ o <- renderWithOptions e NotForked (renderUpdate e)
      done <| case getSecondUserOption o of 
        Forked -> (getFirstUserOption o) ~ defaultDidMove ~ renderNewFork (Annotated a_t t) (Update e')
        NotForked -> (getFirstUserOption o) ~ defaultDidMove ~ (Annotated a_t <| Update e')
    
    Change e -> todo "change"
    -- Change  e -> do
    --   r <- renderConnect style_line Both (editMessage Icon.edit m) (editExpression Icon.database e)
    --   let e' = consolidate m e r
    --   done <| (Change m' e')
    
    View e -> do
      e' ~ o <- renderWithOptions e NotForked (renderView e)
      done <| case getSecondUserOption o of
        Forked -> (getFirstUserOption o) ~ defaultDidMove ~ renderNewFork (Annotated a_t t) (View e')
        NotForked -> (getFirstUserOption o) ~ defaultDidMove ~ (Annotated a_t <| View e')
    
    Watch e -> do
      e' ~ o <- renderWithOptions e NotForked (renderWatch a_t e)
      done <| case getSecondUserOption o of
        Forked -> (getFirstUserOption o) ~ defaultDidMove ~ renderNewFork (Annotated a_t t) (Watch e')
        NotForked -> (getFirstUserOption o) ~ defaultDidMove ~ (Annotated a_t <| Watch e')

    ---- Combinators
    Lift e -> do
      e' <- renderLift e
      done <| NotRemoved ~ defaultDidMove ~ (Annotated a_t <| Lift e')
    Pair [] -> panic "invalid empty pair"
    Choose [] -> panic "invalid empty choose"
    Pair [t] -> panic "invalid single pair, sequencing not implemented yet"
    Choose [t] -> panic "invalid single pair, sequencing not implemented yet"
    Pair ts -> do
      t' ~ o <- renderWithOptions ((this And) ts) NotForked (renderGroup And go ts)
      done <| NotRemoved ~ defaultDidMove ~ case (getSecondUserOption o) of
        Forked -> renderNewFork (Annotated a_t t) (t')
        NotForked -> (Annotated a_t <| t')
    Choose ts -> do
      t' <- renderGroup Or go ts
      done <| (if Array.null ts then Removed else NotRemoved) ~ defaultDidMove ~ (Annotated a_t <| t')

    ---- Extras
    Execute n as -> do
      (n' ~ as') ~ o <- renderWithOptions (n ~ as) NotForked (renderExecute a_t n as)
      done <| case getSecondUserOption o of
        Forked -> (getFirstUserOption o) ~ defaultDidMove ~ renderNewFork (Annotated a_t t) (Execute n' as')
        NotForked -> (getFirstUserOption o) ~ defaultDidMove ~ (Annotated a_t <| Execute n' as') 
    Hole as -> do
      (n' ~ as') ~ o <- renderWithOptions ("??" ~ as) NotForked (renderExecute a_t "??" as)
      if n' == "??" then
        done <| case getSecondUserOption o of
          Forked -> (getFirstUserOption o) ~ defaultDidMove ~ renderNewFork (Annotated a_t t) (Hole as')
          NotForked -> (getFirstUserOption o) ~ defaultDidMove ~ (Annotated a_t <| Hole as')
      else
        done <| case getSecondUserOption o of
          Forked -> (getFirstUserOption o) ~ defaultDidMove ~ renderNewFork (Annotated a_t t) (Execute n' as')
          NotForked -> (getFirstUserOption o) ~ defaultDidMove ~ (Annotated a_t <| Execute n' as')

    ---- Shares
    Assign e1 e2 -> todo "assign"
    -- Assign e1 e2 -> do
    --   r <- renderConnect style_line Push (editExpression Icon.retweet e1) (editExpression Icon.database e2)
    --   let e1' ~ e2' = consolidate e1 e2 r
    --   done <| Annotated ?h (Assign e1' e2')

    Share e -> do
      e' <- renderShare e
      done <| NotRemoved ~ defaultDidMove ~ (Annotated a_t <| Share e')

---- Parts ---------------------------------------------------------------------
renderNewFork :: Checked Task -> Task (Checked Task) -> Checked Task 
renderNewFork (Annotated a_t _) task = 
  (Annotated a_t <| 
    Pair [
      Annotated a_t <| 
        (Step 
          (MIgnore) 
          (Annotated a_t <| task) 
          (Annotated a_t <| 
            Branch ([Constant (B true) ~ (Annotated a_t <| Lift Wildcard)]))
        ) 
    , Builder.item
    ]
  )


---- Options -------------------------------------------------------------------
renderWithOptions :: forall a. a -> IsForked -> Widget a -> Widget (a * UserOptions) -- TODO: better hitboxes to avoid confusion with types
renderWithOptions a isforked widget =
  let 
    contents = Style.column 
      [ renderRemove >-> (\b -> Either.in2 (b ~ NotForked))
      , renderForked isforked >-> (\b -> Either.in2 (NotRemoved ~ b))
      --, renderTaskSelect false >-> (\b -> Either.in2 (false~b))
      ]
  in
    Input.popover After contents (widget >-> Either.in1)
    >-> fix2 a defaultOptions --TODO: Cleaner default values

renderRemove :: Widget (IsRemoved)
renderRemove = 
  Style.element 
  [
    (Attr.onClick ->> Removed) >-> Either.in1 
  ] 
  [ Icon.window_close ]
  >-> fix1 NotRemoved

renderForked :: IsForked -> Widget (IsForked)
renderForked isforked = 
  Style.element 
  [
    (Attr.onClick ->> switch isforked) >-> Either.in1
  ]
  [ forkedSymbol ]
  >-> fix1 isforked
  where
  forkedSymbol = case isforked of
    Forked -> Icon.code_branch -- note: should be flipped code_fork
    NotForked -> Icon.code_branch

---- General ----

-- | [[ * |   n   ]]
-- |     ||
renderStart :: Name -> Parameters -> Widget (Name * Parameters)
renderStart name params =
  Style.column
    [ Style.dot Medium Filled
        [ Style.place Before Medium
            [ Style.row
                [ renderEditor Icon.clipboard (editName name) >-> Either.in1
                , renderParams params ->> Either.in2 params
                ]
            ]
        ]
    , Style.line Solid empty
    ]
    >-> fix2 name params

renderParams :: Parameters -> Widget Unit
renderParams params =
  Style.line Solid [ Style.place Above Small [ Style.column (renderLabels (HashMap.keys params)) ] ]

renderStop :: forall a. Widget a
renderStop = Style.column
  [ Style.line Solid empty
  , Style.dot Medium Filled empty
  ]

-- |      || as
-- |  [[  n  ?]]
renderExecute :: Status -> Name -> Arguments -> Widget (Name * Arguments)
renderExecute status name args =
  Style.column
    [ renderArgs status args >-> Either.in2
    , renderError status
        ( Input.picker
            [ "Builtin" ~ [ "??" ]
            , "Project" ~ (extractContext status |> HashMap.filter isTask |> HashMap.keys |> Array.sort)
            ]
            name
        )
        >-> Either.in1
    ]
    >-> fix2 name args

renderArgs :: Status -> Arguments -> Widget Arguments
renderArgs status args@(ARecord argrow) =
  Input.popover After
    ( Input.card
        []
        [ Style.row [ Concur.traverse renderArg select >-> unselect ] ]
        []
    )
    --NOTE: make sure every vertical line is in a column to make CSS function properly
    (Style.column [ Style.line Solid [ Style.place After Small [ Style.row (renderLabels (HashMap.keys argrow)) ] ] ->> args ])
  where
  --TODO: renaming of variables
  select = status |> extractContext |> HashMap.filter (isFunction >> not) |> HashMap.keys |> map check
  check label = (if HashMap.member label argrow then Yes else No) label
  unselect = catYes >> map (\l -> l ~ Variable l) >> HashMap.fromArray >> ARecord

renderArg :: Selected Label -> Widget (Selected Label)
renderArg sel = case sel of
  Yes l -> Input.chip Primary Remove l ->> No l
  No l -> Input.chip Secondary Add l ->> Yes l

data Selected a
  = Yes a
  | No a

catYes :: forall a. Array (Selected a) -> Array a
catYes = Array.concatMap
  ( case _ of
      Yes x -> [ x ]
      No _ -> []
  )

isYes :: forall a. Selected a -> Bool
isYes = case _ of
  Yes _ -> true
  No _ -> false

renderPossibleArgs :: Status -> Arguments -> Widget Arguments
renderPossibleArgs status args@(ARecord argrow) =
  Style.row
    [ Concur.traverse go labels >-> toArgs ]
  where
  labels = status |> extractContext |> HashMap.filter (isFunction >> not) |> HashMap.keys |> Array.sort
  go label = Input.chip Normal (action label) label ->> label
  action label = if HashMap.member label argrow then Remove else Add
  toArgs labels = ARecord (HashMap.fromArrayBy identity Variable labels)

renderLine :: Array Label -> Widget Unit
renderLine labels =
  Style.line Solid [ Style.place After Small [ Style.row (renderLabels labels) ] ]

-- | || (( a_1 .. a_n ))
renderLabels :: Array Label -> Array (Widget Unit)
renderLabels =
  map (Input.chip Normal None)

renderContext :: Status -> String
renderContext = extractContext >> HashMap.filter (isFunction >> not) >> HashMap.toArrayBy (~) >> Array.sortBy (compare `on` fst) >> foldMap go
  where
  go (n ~ t) = n ++ " : " ++ show t ++ "\n"

---- Steps ----

-- |   || as
-- |   V
renderStep :: Status -> Cont -> Match -> Widget (DidMoveOptions * Cont * Match)
renderStep status cont match@(MRecord row) =
  Style.column
    [ renderLine labels ->> (Either.in3 match)
    , Input.popover After contents <| Input.popover Before (Text.code "TopHat" (renderContext status)) <|
        Style.element
          [ void Attr.onClick ->> Either.in2 (switch cont)
          , void Attr.onDoubleClick ->> Either.in2 New
          ]
          [ Style.triangle (style cont) empty ]
    ]
    >-> fix3 defaultDidMove cont match
  where
  contents = 
    Style.column 
      [ Style.element 
        [void Attr.onClick ->> Either.in1 (MovedUp ~ NotMovedDown)]
        [Icon.arrow_up]
      , Style.element
        [void Attr.onClick ->> Either.in1 (NotMovedUp ~ MovedDown)]
        [Icon.arrow_down]
      ]
  labels = HashMap.values row |> map getBinds |> Array.catMaybes
  getBinds = case _ of
    MBind n -> Just n
    _ -> Nothing
renderStep _ _ _ = todo "other matches in step rendering"

renderGuardableStep :: Status -> IsGuarded -> Expression -> Cont -> Match -> Widget (IsGuarded * Expression * (DidMoveOptions * Cont * Match))
renderGuardableStep status isguarded expr cont match@(MRecord row) = 
  Style.column
    ( [Input.popover After contents (renderStep status cont match >-> Either.in3)]
      ++ guard
    )
    >-> fix3 isguarded expr (defaultDidMove ~ cont ~ match)
  where
  contents =
    Style.column 
    [ (renderGuardButton isguarded >-> Either.in1)
    ]
  guard = case isguarded of
    Guarded -> [(renderOption status expr) >-> Either.in2]
    NotGuarded -> []
renderGuardableStep _ _ _ _ _ = todo "no"

renderOption :: Status -> Expression -> Widget Expression
renderOption status guard =
  Style.line Dashed
    [ Style.place After Small [ renderGuard status guard ] ]

renderOptionWithLabel :: Status -> Label -> Expression -> Widget (Label * Expression)
renderOptionWithLabel status label guard =
  Style.line Dashed
    [ Style.place After Small [ renderLabel label >-> Either.in1, renderGuard status guard >-> Either.in2 ]
    -- , Style.place Before [  ] >-> Either.in1
    ]
    >-> fix2 label guard

renderSingleUnguarded :: forall a. (a -> Widget (IsRemoved * DidMoveOptions * a)) -> Status -> Cont -> Match -> a -> a -> Widget ((IsGuarded * Expression * (DidMoveOptions * Cont * Match)) * (IsRemoved * DidMoveOptions * a) * (IsRemoved * DidMoveOptions * a))
renderSingleUnguarded render status cont match sub1 sub2 =
  Style.column
    [ render sub1 >-> Either.in2
    , renderGuardableStep status NotGuarded (Constant (B true)) cont match >-> Either.in1
    , render sub2 >-> Either.in3
    ]
    >-> fix3 (NotGuarded ~ (Constant (B true)) ~ (defaultDidMove ~ cont ~ match)) (NotRemoved ~ defaultDidMove ~ sub1) (NotRemoved ~ defaultDidMove ~ sub2)

renderSingleBranch :: RemovedRenderer -> Status -> Match -> Checked Task -> Expression * Checked Task -> Widget(IsDoubled * (IsGuarded * Expression * (DidMoveOptions * Cont * Match)) * (IsRemoved * DidMoveOptions * Checked Task) * (IsRemoved * DidMoveOptions * Checked Task))
renderSingleBranch render status match sub1 branch@(expr ~ sub2) = 
  Style.element [
    void Attr.onDoubleClick ->> Either.in1 Doubled
  ]
  [ Style.column
      [ render sub1 >-> Either.in3
      , renderGuardableStep status Guarded expr Hurry match >-> (\(g ~ e ~ (h ~ c ~ m)) -> g ~ e ~ (h ~ c ~ m)) >-> Either.in2
      , render sub2 >-> Either.in4
      ]
  ]
    >-> fix4 NotDoubled (Guarded ~ expr ~ (defaultDidMove ~ Hurry ~ match)) (NotRemoved ~ defaultDidMove ~ sub1) (NotRemoved ~ defaultDidMove ~ sub2)

renderEnd :: forall a. (a -> Widget (IsRemoved * DidMoveOptions * a)) -> Status -> Match -> a -> Widget (Cont * Match * (IsRemoved * DidMoveOptions * a))
renderEnd render status args@(MRecord row) subtask =
  Style.column
    [ render subtask >-> Either.in3
    , renderLine (HashMap.keys row) ->> Either.in2 args
    , Input.popover Before (Text.code "TopHat" (renderContext status)) <|
        Style.element [ void Attr.onDoubleClick ->> Either.in1 New ]
          [ Style.triangle (style Hurry) empty ]
    ]
    >-> fix3 Hurry args (NotRemoved ~ defaultDidMove ~ subtask)
renderEnd render status args@(MIgnore) subtask =
  Style.column
    [ render subtask >-> Either.in3
    , renderLine [] ->> Either.in2 args
    , Input.popover Before (Text.code "TopHat" (renderContext status)) <|
        Style.element [ void Attr.onDoubleClick ->> Either.in1 New ]
          [ Style.triangle (style Hurry) empty ]
    ]
    >-> fix3 Hurry args (NotRemoved ~ defaultDidMove ~ subtask)
renderEnd _ _ _ _ = todo "other matches in end rendering"

---- Branches ----

renderBranches :: RemovedRenderer -> Status -> Match -> Checked Task -> Branches (Checked Task) -> Widget ((DidMoveOptions * Cont * Match) * (IsRemoved * DidMoveOptions * Checked Task) * Branches (Checked Task))
renderBranches render status match subtask branches =
  Style.column
    [ render subtask >-> Either.in2
    , renderStep status Hurry match >-> Either.in1
    , Style.element 
        [ void Attr.onDoubleClick ->> Either.in3 (branches ++ [ Builder.always ~ Builder.item ]) 
        ]
        [ Style.branch
            [ Concur.traverse (renderBranch (fixgo << render)) ((\(expr ~ t) -> NotCondensed ~ expr ~ t) <-< branches) >-> mapping >-> Either.in3 ]
        ]
    ]
      >-> fix3 (defaultDidMove ~ Hurry ~ match) (NotRemoved ~ defaultDidMove ~ subtask) branches
    where 
    mapping = (\arr -> arr
      |> Array.filter (\(con ~ _ ~ _) -> con == NotCondensed) 
      >-> (\(_ ~ e ~ t) -> e ~ t)) 

renderBranch :: Renderer -> IsCondensed * Expression * Checked Task -> Widget (IsCondensed * Expression * Checked Task)
renderBranch render (iscondensed ~ guard ~ subtask@(Annotated status _)) =
  Style.column
    [ Input.popover Above contents <| Style.element [] [renderOption status guard >-> Either.in2]
    , Style.line Dashed empty
    , Style.line Dashed empty
    , render subtask >-> Either.in3
    , Style.line Solid empty
    ]
    >-> fix3 NotCondensed guard subtask
  where
  contents = 
    Style.element 
      [
        Attr.onClick ->> Condensed >-> Either.in1 
      ]
      [
        Icon.code_branch
      ]
--   Style.column
--     [ Style.line Dashed [ Style.place After (Input.addon Icon.question (Input.entry Small ?holder ?value)) ]
--     , renderTask task
--     ]

renderSelects :: RemovedRenderer -> Status -> Match -> Checked Task -> LabeledBranches (Checked Task) -> Widget ((DidMoveOptions * Cont * Match) * (IsRemoved * DidMoveOptions * Checked Task) * LabeledBranches (Checked Task))
renderSelects render status match subtask branches =
  Style.column
    [ render subtask >-> Either.in2
    , renderStep status Delay match >-> Either.in1
    , Style.element [ void Attr.onDoubleClick ->> Either.in3 (branches ++ [ "Continue" ~ Builder.always ~ Builder.item ]) ]
      [ Style.branch 
          [ Concur.traverse (renderSelect (fixgo << render)) ((\(l ~ e ~ t) -> NotCondensed ~ l ~ e ~ t) <-< branches) >-> mapping >-> Either.in3 ]  
      ]
    ]
    >-> fix3 (defaultDidMove ~ Delay ~ match) (NotRemoved ~ defaultDidMove ~ subtask) branches
  where 
  mapping = (\arr -> arr
    |> Array.filter (\(con ~ _ ~ _ ~ _) -> con == NotCondensed) 
    >-> (\(_ ~ l ~ e ~ t) -> l ~ e ~ t)) 

renderSelect :: Renderer -> IsCondensed * Label * Expression * Checked Task -> Widget (IsCondensed * Label * Expression * Checked Task)
renderSelect render (iscondensed ~ label ~ guard ~ subtask@(Annotated status _)) =
  Style.column
    [ Input.popover Above contents <| Style.element [] [renderOptionWithLabel status label guard >-> Either.in2]
    , Style.line Dashed empty
    , Style.line Dashed empty
    , render subtask >-> Either.in3
    , Style.line Solid empty
    ]
    >-> fix3 NotCondensed (label ~ guard) subtask
    >-> assoc4
  where
  contents = 
    Style.element 
      [
        Attr.onClick ->> Condensed >-> Either.in1 
      ]
      [
        Icon.code_branch
      ]

renderSingleSelect :: RemovedRenderer -> Status -> Match -> Checked Task -> Label * Expression * Checked Task -> Widget ( (IsDoubled) * (IsGuarded * (Label * Expression) * (DidMoveOptions * Cont * Match)) * (IsRemoved * DidMoveOptions * Checked Task) * (IsRemoved * DidMoveOptions * Checked Task) )
renderSingleSelect render status match sub1 branch@(label ~ expr ~ sub2) = 
  Style.element [
    void Attr.onDoubleClick ->> Either.in1 (Doubled)
  ]
  [ Style.column
      [ render sub1 >-> Either.in3
      , renderGuardedSelect status Guarded label expr Delay match >-> Either.in2
      , render sub2 >-> Either.in4
      ]
  ]
    >-> fix4 NotDoubled (Guarded ~ (label ~ expr) ~ (defaultDidMove ~ Delay ~ match)) (NotRemoved ~ defaultDidMove ~ sub1) (NotRemoved ~ defaultDidMove ~ sub2)

renderGuardedSelect :: Status -> IsGuarded -> Label -> Expression -> Cont -> Match -> Widget (IsGuarded * (Label * Expression) * (DidMoveOptions * Cont * Match))
renderGuardedSelect status isguarded label expr cont match@(MRecord row) = 
  Style.column
    ([ Input.popover After (renderGuardButton isguarded >-> Either.in1) <| (renderStep status cont match >-> Either.in3)]
    ++ guard ) 
        >-> fix3 isguarded (label ~ expr) (defaultDidMove ~ cont ~ match)
  where
  guard = case isguarded of
    Guarded -> 
      [ renderOptionWithLabel status label expr >-> Either.in2
        , Style.line Dashed empty                                 --hacky extra line to ensure enough space
      ] 
    NotGuarded -> []
renderGuardedSelect _ _ _ _ _ _ = todo "no"

renderGuardButton :: IsGuarded -> Widget(IsGuarded)
renderGuardButton isguarded = 
  Style.column
      [ Style.element 
        [
          Attr.onClick ->> Either.in1 (switch isguarded) 
        ]
        [
          Icon.question
        ]
      ]
    >-> fix1 isguarded

---- Combinators ----

-- | ==============
-- |  t_1 ... t_n
-- | =============
-- renderGroup :: forall a. Stroke -> (a -> Widget a) -> Array a -> Widget (Array a)
renderGroup :: Par -> RemovedRenderer -> Array (Checked Task) -> Widget (Task (Checked Task))
renderGroup par render tasks =
  Style.element
    [ void Attr.onClick ->> other par tasks
    , void Attr.onDoubleClick ->> this par (tasks ++ [ Builder.item ])
    ]
    [ Style.group (stroke par)
        [ Concur.traverse (renderSingleGroup (fixgo << render)) ((\t -> NotCondensed ~ t) <-< tasks) >-> mapping >-> this par
        -- , Input.button Action Secondary Small "+" ->> this par (tasks ++ [ Builder.item ])
        ]
    ]
  where 
  mapping = (\arr -> arr
    |> Array.filter (\(c ~ _) -> c == NotCondensed) 
    >-> snd) 

renderSingleGroup :: Renderer -> IsCondensed * Checked Task -> Widget(IsCondensed * Checked Task) 
renderSingleGroup render (iscondensed ~ subtask) =
  Style.column
    [ Input.popover Above contents <| Style.element [] [Style.column [Style.line Solid empty]]
    , render subtask >-> Either.in2
    , Style.line Solid empty
    ]
    >-> fix2 NotCondensed subtask
  where
  contents = 
    Style.element 
      [
        Attr.onClick ->> Condensed >-> Either.in1 
      ]
      [
        Icon.code_branch
      ]

---- Editors ----

-- | [[ i |   w   ]]
renderEditor :: forall a. Widget a -> Widget a -> Widget a
renderEditor =
  Input.addon Medium

renderEnter :: Labeled BasicType -> Name -> Widget Name
renderEnter types name =
  --Style.column
  --[ Style.line Solid []
  --, renderEditor Icon.pen (selectType types name)
  --]
  renderEditor Icon.pen (selectType types name)

renderUpdate :: Expression -> Widget Expression
renderUpdate expr =
  renderEditor Icon.edit (editExpression expr)

renderView :: Expression -> Widget Expression
renderView expr =
  renderEditor Icon.eye (editExpression expr)

renderLift :: Expression -> Widget Expression
renderLift expr =
  renderEditor Icon.check_double (editExpression expr)

renderShare :: Expression -> Widget Expression
renderShare expr =
  renderEditor Icon.retweet (editExpression expr)

renderGuard :: Status -> Expression -> Widget Expression
renderGuard status expr =
  renderError status
    (Input.addon Small Icon.question (editGuard expr))

renderLabel :: Label -> Widget Label
renderLabel = editLabel

---- Shares --------------------------------------------------------------------

renderWatch :: Status -> Expression -> Widget Expression
renderWatch status expr =
  renderEditor Icon.eye <|
    Style.place After Large
      [ Style.row
          [ Style.dot Small Filled []
          , Style.line Solid []
          , renderEditor Icon.database (status |> extractContext |> flip selectRef expr)
          ]
      ]

---- Helpers -------------------------------------------------------------------

renderError :: forall a. Status -> Widget a -> Widget a
renderError (Failure _ err) w =
  -- Style.has Error [ Input.popover Before (Input.card [ Text.subsubhead "Error" ] [ Text.code "TopHat" (show err) ] []) w ]
  Style.has Error [ Input.tooltip Before (show err) w ]
renderError _ w =
  Style.has Normal [ w ]

---- Entries -------------------------------------------------------------------

-- | [[  n  ?]]
selectType :: Typtext -> Name -> Widget Name
selectType types name =
  Input.picker
    [ "Builtin" ~ Array.sort (HashMap.keys aliases)
    , "Project" ~ Array.sort (HashMap.keys types)
    ]
    name

selectRef :: Context -> Expression -> Widget Expression
selectRef context (Variable name) =
  Input.picker
    [ "Shares" ~ Array.sort (context |> HashMap.filter isReference |> HashMap.keys) ]
    name >-> Variable
selectRef _ _ = todo "unnamed references not supported"

-- | [[  e  ]]
editExpression :: Expression -> Widget Expression
editExpression expr =
  Input.entry Medium "enter an expression..." (show expr) ->> Variable "x"

editGuard :: Expression -> Widget Expression
editGuard expr =
  Input.entry Small "enter an expression..." (show expr) ->> Variable "x"

editName :: Name -> Widget Name
editName name =
  Input.entry Medium "enter a name..." name

editLabel :: Label -> Widget Label
editLabel lbl =
  Input.entry Small "enter a label..." lbl

{-
-- |       V
-- | ==============
-- |  w_1 ... w_n
-- | =============
renderContinuation :: forall a. Kind -> ShapeStyle () -> (a -> Widget a) -> Array a -> Widget (Array a)
renderContinuation k s f ws =
  Style.column
    [ Style.head Downward style_line
    -- TODO either group or single, depending on count
    , renderGroup s f ws
    ]
-- |  r
-- |  | m
-- |  f
renderStep :: Checked Task -> Checked Task -> Widget (Both (Checked Task))
renderStep t1 t2 = do
  Style.column
    [ go t1 >-> Left
    , Style.line
    , go t2 >-> Right
    ]
-- -- | w_1 *--* w_2
-- renderConnect :: forall a b r. LineStyle r -> Connect -> Widget a -> Widget b -> Widget (Either a b)
-- renderConnect s m a b = do
--   Style.row [ a >-> Left, line, b >-> Right ]
--   where
--   line = case m of
--     Pull -> Style.row [ dot, connection ]
--     Push -> Style.row [ connection, dot ]
--     Both -> Style.row [ dot, connection, dot ]
--   --TODO: factor out style
--   dot = Style.dot 0.33 "black"
--   connection = Style.line Style.Horizontal 4.0 s
-- data Connect
--   = Pull
--   | Push
--   | Both
---- Inputs --------------------------------------------------------------------
-- | [[ i m ]]
editMessage :: Icon ->  Widget Message
editMessage i m =
  renderBox style_box
    [ i, Input.entry m m ]
editLabels :: Context -> Arguments -> Widget Arguments
editLabels g (ARecord as) =
  --TODO show labels and expressions
  Style.column (map (show >> text) (HashMap.keys as))
-- -- | [[ i n ]]
-- selectValues :: Context -> Icon -> Labeled Name -> Widget (Labeled Name)
-- selectValues g i ns = do
--   _ <- renderBox style_box []
--   done ns
-}

---- Helpers -------------------------------------------------------------------

type Both a
  = Either a a

fix1 :: forall a. a -> a + Void -> a 
fix1 _1 = case _ of 
  Left _1' -> _1' 
  Right _ -> _1 

fix2 :: forall a b. a -> b -> a + b + Void -> a * b
fix2 _1 _2 = case _ of
  Left _1' -> _1' ~ _2
  Right (Left _2') -> _1 ~ _2'
  Right (Right contra) -> absurd contra

fix3 :: forall a b c. a -> b -> c -> a + b + c + Void -> a * b * c
fix3 _1 _2 z = case _ of
  Left _1' -> _1' ~ _2 ~ z
  Right (Left _2') -> _1 ~ _2' ~ z
  Right (Right (Left _3')) -> _1 ~ _2 ~ _3'
  Right (Right (Right contra)) -> absurd contra

fix4 :: forall a b c d. a -> b -> c -> d -> a + b + c + d + Void -> a * b * c * d
fix4 _1 _2 _3 _4 = case _ of
  Left _1' -> _1' ~ _2 ~ _3 ~ _4
  Right (Left _2') -> _1 ~ _2' ~ _3 ~ _4
  Right (Right (Left _3')) -> _1 ~ _2 ~ _3' ~ _4
  Right (Right (Right (Left _4'))) -> _1 ~ _2 ~ _3 ~ _4'
  Right (Right (Right (Right contra))) -> absurd contra

reorder3 :: forall a b c. a * b * c -> b * c * a
reorder3 (a ~ b ~ c) = b ~ c ~ a

reorder4 :: forall a b c d. a * b * c * d -> c * d * a * b
reorder4 (a ~ b ~ c ~ d) = (c ~ d ~ a ~ b)

reorder6 :: forall a b c d e f. a * b * c * d * e * f -> e * f * a * b * c * d
reorder6 (a ~ b ~ c ~ d ~ e ~ f) = (e ~ f ~ a ~ b ~ c ~ d)

assoc :: forall a b c. (a * b) * c -> a * (b * c)
assoc ((a ~ b) ~ c) = a ~ b ~ c

assoc4 :: forall a b c d. a * (b * c) * d -> a * b * c * d
assoc4 (a ~ (b ~ c) ~ d) = a ~ b ~ c ~ d

flat4 :: forall a b c d. a -> b -> (c * d) -> a * b * c * d
flat4 a b (c ~ d) = (a ~ b ~ c ~ d)

data Par
  = And
  | Or

this :: forall a. Par -> Array a -> Task a
this And = Pair
this Or = Choose

other :: forall a. Par -> Array a -> Task a
other And = Choose
other Or = Pair

stroke :: Par -> Stroke
stroke And = Solid
stroke Or = Double


data Cont
  = Hurry
  | Delay
  | New --NOTE: hacky...

style :: Cont -> Style
style Hurry = Filled
style Delay = Outlined
style New = Filled -- NOTE: just to make it total...

data IsGuarded 
  = Guarded
  | NotGuarded

data IsRemoved
  = Removed
  | NotRemoved

data IsCondensed
  = Condensed
  | NotCondensed

data IsForked
  = Forked
  | NotForked

data IsDoubled 
  = Doubled
  | NotDoubled

class Switch a where
  switch :: a -> a

instance Switch Par where
  switch And = Or
  switch Or = And

instance Switch Cont where
  switch Hurry = Delay
  switch Delay = Hurry
  switch New = New

instance Switch IsGuarded where
  switch Guarded = NotGuarded
  switch NotGuarded = Guarded

instance Switch IsForked where
  switch Forked = NotForked
  switch NotForked = Forked


instance Eq IsCondensed where
  eq Condensed Condensed = true
  eq NotCondensed NotCondensed = true
  eq _ _ = false


addLabels :: forall f v. Functor f => f v -> f (String * v)
addLabels = map ("" ~ _)

removeLabels :: forall f v k. Functor f => f (k * v) -> f v
removeLabels = map snd


data DidMoveUp
  = MovedUp
  | NotMovedUp

data DidMoveDown
  = MovedDown
  | NotMovedDown

type DidMoveOptions = DidMoveUp * DidMoveDown

defaultDidMove :: DidMoveOptions
defaultDidMove = NotMovedUp ~ NotMovedDown

getFirstMoved :: DidMoveOptions -> DidMoveUp 
getFirstMoved = fst 

getSecondMoved :: DidMoveOptions -> DidMoveDown
getSecondMoved = snd


type UserOptions = IsRemoved * IsForked

defaultOptions :: UserOptions
defaultOptions = NotRemoved ~ NotForked

getFirstUserOption :: UserOptions -> IsRemoved 
getFirstUserOption = fst 

getSecondUserOption :: UserOptions -> IsForked
getSecondUserOption = snd
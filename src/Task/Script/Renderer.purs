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

fixgo :: Widget (Bool * Checked Task) -> Widget (Checked Task)
fixgo g = do
  (_~t) <- g 
  done <| t

renderTask :: Context -> Typtext -> Renderer
renderTask g s t = Style.column
  [ fixgo <| go t
  ]
  where
  go :: Checked Task -> Widget (ShouldRemove * Checked Task)
  go (Annotated a_t t) = case t of
    ---- Steps
    -- NOTE:
    -- Be aware of the INVARIANT: Branch and Select need to be inside a Step.
    
    -- m:                           match, aka params next to line
    -- t1:                          task before the step
    -- t2/(some task definition):   task after the step

    -- for task types, see Syntax.purs


    -- case following subtask::unguarded Branch of Lift (why???)
    Step m t1 orig@(Annotated a_b (Branch [ Constant (B true) ~ Annotated a_l (Lift e) ])) -> do
      c' ~ m' ~ (b1' ~ t1') <- renderEnd go a_t m t1
      done <| case b1' of 
        true -> false ~ (Annotated a_l (Lift e) )
        false -> false ~ ( Annotated a_t <-< Step m' t1' <| case c' of
          New -> Builder.new orig
          _ -> orig)

    -- case following subtask::unguarded Branch of other
    Step m t1 orig@(Annotated a_b (Branch [ Constant (B true) ~ t2 ])) -> do
      c' ~ m' ~ (b1' ~ t1') ~ (_ ~ t2') ~ g' ~ e' <- renderSingle go a_t false (Constant (B true)) Hurry m t1 t2
      done <| case b1' of
        true -> false ~ t2'
        false -> false ~ (Annotated a_t <| Step m' t1' <| case (c' ~ g') of
            (Hurry ~ true) -> Annotated a_b <| Branch [ Constant (B false) ~ t2' ]
            (Hurry ~ false) -> Annotated a_b <| Branch [ Constant (B true) ~ t2' ]
            (Delay ~ true) -> Annotated a_b <| Select [ "Continue" ~ Constant (B false) ~ t2' ]
            (Delay ~ false) -> Annotated a_b <| Select [ "Continue" ~ Constant (B true) ~ t2' ]
            (New ~ _) -> Builder.new orig)

    -- case following subtask::guarded Branch with 1 branch
    Step m t1 orig@(Annotated a_b (Branch [ e ~ t2 ])) -> do
      c' ~ m' ~ (b1' ~ t1') ~ (_ ~ t2') ~ g' ~ e' <- renderSingle go a_t true e Hurry m t1 t2
      done <| case b1' of
        true -> false ~ t2'
        false -> false ~ (Annotated a_t <| Step m' t1' <| case (c' ~ g') of
          (Hurry ~ true) -> Annotated a_b <| Branch [Constant (B false) ~ t2']
          (Hurry ~ false) -> Annotated a_b <| Branch [ Constant (B true) ~ t2' ]
          (Delay ~ true) -> Annotated a_b <| Select ["Continue" ~ Constant (B false) ~ t2']
          (Delay ~ false) -> Annotated a_b <| Select ["Continue" ~ Constant (B true) ~ t2' ]
          (New ~ _) -> Builder.new orig)

    -- case following subtask::guarded Branch with more than 1 branch
    Step m t1 orig@(Annotated a_b (Branch bs)) -> do
      c' ~ m' ~ t1' ~ bs' <- renderBranches (fixgo << go) a_t m t1 bs
      done <| false ~ (Annotated a_t <| Step m' t1' <| case c' of
        Hurry -> Annotated a_b <| Branch bs'
        Delay -> Annotated a_b <| Select (addLabels bs')
        New -> Builder.new orig)

    -- case following subtask::unguarded Select
    Step m t1 orig@(Annotated a_b (Select [ "Continue" ~ Constant (B true) ~ t2 ])) -> do
      c' ~ m' ~ (b1' ~ t1') ~ (_ ~ t2') ~ g' ~ e' <- renderSingle go a_t false (Constant (B true)) Delay m t1 t2
      done <| case b1' of
        true -> false ~ t2'
        false -> false ~ (Annotated a_t <| Step m' t1' <| case (c' ~ g') of
          (Hurry ~ true) -> Annotated a_b <| Branch [ Constant (B false) ~ t2' ]
          (Hurry ~ false) -> Annotated a_b <| Branch [ Constant (B true) ~ t2' ]
          (Delay ~ true) -> Annotated a_b <| Select [ "Continue" ~ Constant (B false) ~ t2' ]
          (Delay ~ false) -> Annotated a_b <| Select [ "Continue" ~ Constant (B true) ~ t2' ]
          (New ~ _) -> Builder.new orig)

    --case following subtask::guarded Select with 1 branch
    Step m t1 orig@(Annotated a_b (Select [l ~ e ~ t2])) -> do
      c' ~ m' ~ (b1' ~ t1') ~ (_ ~ t2') ~ g' ~ l' ~ e' <- renderSingleSelect go a_t true m t1 (l ~ e ~ t2)
      done <| case b1' of
        true -> false ~ t2'
        false -> false ~ (Annotated a_t <| Step m' t1' <| case (c' ~ g') of
          (Hurry ~ true) -> Annotated a_b <| Branch ([Constant (B false) ~ t2'])
          (Hurry ~ false) -> Annotated a_b <| Branch ([Constant (B true) ~ t2' ])
          (Delay ~ true) -> Annotated a_b <| Select [l' ~ Constant (B false) ~ t2']
          (Delay ~ false) -> Annotated a_b <| Select [l' ~ Constant (B true) ~ t2' ]
          (New ~ _) -> Builder.new orig)

    --case following subtask::guarded Select with more than 1 branch
    Step m t1 orig@(Annotated a_b (Select bs)) -> do
      c' ~ m' ~ t1' ~ bs' <- renderSelects (fixgo << go) a_t m t1 bs
      done <| false ~ (Annotated a_t <| Step m' t1' <| case c' of
        Hurry -> Annotated a_b <| Branch (removeLabels bs')
        Delay -> Annotated a_b <| Select bs'
        New -> Builder.new orig)

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
      n' ~ o <- renderWithOptions n (renderEnter s n)
      done <| (getFirstUserOption o) ~ (Annotated a_t <| Enter n')
    Update e -> do
      e' ~ o <- renderWithOptions e (renderUpdate e)
      done <| (getFirstUserOption o) ~ (Annotated a_t <| Update e')
    Change e -> todo "change"
    -- Change  e -> do
    --   r <- renderConnect style_line Both (editMessage Icon.edit m) (editExpression Icon.database e)
    --   let e' = consolidate m e r
    --   done <| (Change m' e')
    View e -> do
      e' ~ o <- renderWithOptions e (renderView e)
      done <| (getFirstUserOption o) ~ (Annotated a_t <| View e')
    Watch e -> do
      e' ~ o <- renderWithOptions e (renderWatch a_t e)
      done <| (getFirstUserOption o) ~ (Annotated a_t <| Watch e')

    ---- Combinators
    Lift e -> do
      e' <- renderLift e
      done <| false ~ (Annotated a_t <| Lift e')
    Pair ts -> do
      t' <- renderGroup And (fixgo << go) ts
      done <| (if Array.null ts then true else false) ~ (Annotated a_t <| t')
    Choose ts -> do
      t' <- renderGroup Or (fixgo << go) ts
      done <| (if Array.null ts then true else false) ~ (Annotated a_t <| t')

    ---- Extras
    Execute n as -> do
      (n' ~ as') ~ o <- renderWithOptions (n ~ as) (renderExecute a_t n as)
      done <| (getFirstUserOption o) ~ (Annotated a_t <| Execute n' as') 
    Hole as -> do
      (n' ~ as') ~ o <- renderWithOptions ("??" ~ as) (renderExecute a_t "??" as)
      if n' == "??" then
        done <| (getFirstUserOption o) ~ (Annotated a_t <| Hole as')
      else
        done <| (getFirstUserOption o) ~ (Annotated a_t <| Execute n' as')

    ---- Shares
    Assign e1 e2 -> todo "assign"
    -- Assign e1 e2 -> do
    --   r <- renderConnect style_line Push (editExpression Icon.retweet e1) (editExpression Icon.database e2)
    --   let e1' ~ e2' = consolidate e1 e2 r
    --   done <| Annotated ?h (Assign e1' e2')

    Share e -> do
      e' <- renderShare e
      done <| false ~ (Annotated a_t <| Share e')

---- Parts ---------------------------------------------------------------------

---- Options -------------------------------------------------------------------
renderWithOptions :: forall a. a -> Widget a -> Widget (a * UserOptions) -- TODO: better hitboxes to avoid confusion with types
renderWithOptions a widget =
  let 
    contents = Style.column 
      [ renderRemove >-> (\b -> Either.in2 (b~false))
      --, renderTaskSelect false >-> (\b -> Either.in2 (false~b))
      ]
  in
    Input.popover After contents (widget >-> Either.in1)
    >-> fix2 a defaultOptions --TODO: Cleaner default values

renderRemove :: Widget (ShouldRemove)
renderRemove = 
  Style.element 
  [
    (Attr.onClick ->> true) >-> Either.in1 
  ] 
  [ Icon.window_close ]
  >-> fix1 false 

--renderTaskSelect :: IsSelected -> Widget (IsSelected)
--renderTaskSelect s = Input.checkbox "" s

defaultOptions :: ShouldRemove * Bool --placeholder Bool
defaultOptions = false ~ false

type UserOptions = ShouldRemove * Bool --placeholder Bool

type ShouldRemove = Bool 

getFirstUserOption :: UserOptions -> ShouldRemove 
getFirstUserOption = fst 

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
renderStep :: Status -> Cont -> Match -> Widget (Cont * Match)
renderStep status cont match@(MRecord row) =
  Style.column
    [ renderLine labels ->> (Either.in2 match)
    , Input.popover Before (Text.code "TopHat" (renderContext status)) <|
        Style.element
          [ void Attr.onClick ->> Either.in1 (switch cont)
          , void Attr.onDoubleClick ->> Either.in1 New
          ]
          [ Style.triangle (style cont) empty ]
    ]
    >-> fix2 cont match
  where
  labels = HashMap.values row |> map getBinds |> Array.catMaybes
  getBinds = case _ of
    MBind n -> Just n
    _ -> Nothing
renderStep _ _ _ = todo "other matches in step rendering"

renderGuardedStep :: Status -> IsGuarded -> Expression -> Cont -> Match -> Widget (IsGuarded * Expression * (Cont * Match))
renderGuardedStep status isguarded expr cont match@(MRecord row) = 
  Style.column
    ( [Input.popover After (renderGuardButton isguarded >-> Either.in1) (renderStep status cont match >-> Either.in3)]
      ++ guard
    )
    >-> fix3 isguarded expr (cont ~ match)
  where
  guard = case isguarded of
    true -> [(renderOption status expr) >-> Either.in2, Style.line Solid empty] -- extra line for consistency with renderGuardedSelect
    false -> []
renderGuardedStep _ _ _ _ _ = todo "no"

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

renderSingle :: forall a. (a -> Widget (Bool * a)) -> Status -> IsGuarded -> Expression -> Cont -> Match -> a -> a -> Widget (Cont * Match * (Bool * a) * (Bool * a) * IsGuarded * Expression)
renderSingle render status isguarded expr cont match sub1 sub2 =
  Style.column
    [ render sub1 >-> Either.in1
    , renderGuardedStep status isguarded expr cont match >-> Either.in3
    , render sub2 >-> Either.in2
    ]
    >-> fix3 (false ~ sub1) (false ~ sub2) (isguarded ~ expr ~ (cont ~ match))
    >-> reorder6

renderEnd :: forall a. (a -> Widget (Bool * a)) -> Status -> Match -> a -> Widget (Cont * Match * (Bool * a))
renderEnd render status args@(MRecord row) subtask =
  Style.column
    [ render subtask >-> Either.in3
    , renderLine (HashMap.keys row) ->> Either.in2 args
    , Input.popover Before (Text.code "TopHat" (renderContext status)) <|
        Style.element [ void Attr.onDoubleClick ->> Either.in1 New ]
          [ Style.triangle (style Hurry) empty ]
    ]
    >-> fix3 Hurry args (false ~ subtask)
renderEnd _ _ _ _ = todo "other matches in end rendering"

---- Branches ----

renderBranches :: Renderer -> Status -> Match -> Checked Task -> Branches (Checked Task) -> Widget (Cont * Match * Checked Task * Branches (Checked Task))
renderBranches render status match subtask branches =
  Style.column
    [ render subtask >-> Either.in1
    , renderStep status Hurry match >-> Either.in3
    , Style.element [ void Attr.onDoubleClick ->> Either.in2 (branches ++ [ Builder.always ~ Builder.item ]) ]
        [ Style.branch
            [ Concur.traverse (renderBranch render) branches >-> Either.in2 ]
        ]
    ]
    >-> fix3 subtask branches (Hurry ~ match)
    >-> reorder4

renderBranch :: Renderer -> Expression * Checked Task -> Widget (Expression * Checked Task)
renderBranch render (guard ~ subtask@(Annotated status _)) =
  Style.column
    [ renderOption status guard >-> Either.in1
    , render subtask >-> Either.in2
    , Style.line Solid empty
    ]
    >-> fix2 guard subtask

--   Style.column
--     [ Style.line Dashed [ Style.place After (Input.addon Icon.question (Input.entry Small ?holder ?value)) ]
--     , renderTask task
--     ]

renderSelects :: Renderer -> Status -> Match -> Checked Task -> LabeledBranches (Checked Task) -> Widget (Cont * Match * Checked Task * LabeledBranches (Checked Task))
renderSelects render status match subtask branches =
  Style.column
    [ render subtask >-> Either.in1
    , renderStep status Delay match >-> Either.in3
    , Style.element [ void Attr.onDoubleClick ->> Either.in2 (branches ++ [ "Continue" ~ Builder.always ~ Builder.item ]) ]
      [ Style.branch 
          [ Concur.traverse (renderSelect render) branches  >-> Either.in2 ]
      ]
    ]
    >-> fix3 subtask branches (Delay ~ match)
    >-> reorder4

renderSelect :: Renderer -> Label * Expression * Checked Task -> Widget (Label * Expression * Checked Task)
renderSelect render (label ~ guard ~ subtask@(Annotated status _)) =
  Style.column
    [ renderOptionWithLabel status label guard >-> Either.in2
    -- , Style.line Solid empty
    , render subtask >-> Either.in1
    , Style.line Solid empty
    ]
    >-> fix2 subtask (label ~ guard)
    >-> reorder3

renderSingleSelect :: forall a. (a -> Widget (Bool * a)) -> Status -> IsGuarded -> Match -> a -> Label * Expression * a -> Widget (Cont * Match * (Bool * a) * (Bool * a) * IsGuarded * (Label * Expression))
renderSingleSelect render status isguarded match sub1 (label ~ expr ~ sub2) = 
  Style.column
    [ render sub1 >-> Either.in1
    , renderGuardedSelect status isguarded label expr Delay match >-> Either.in3
    , render sub2 >-> Either.in2
    ]
    >-> fix3 (false ~ sub1) (false ~ sub2) (isguarded ~ (label ~ expr) ~ (Delay ~ match))
    >-> reorder6

renderGuardedSelect :: Status -> IsGuarded -> Label -> Expression -> Cont -> Match -> Widget (IsGuarded * (Label * Expression) * (Cont * Match))
renderGuardedSelect status isguarded label expr cont match@(MRecord row) = 
  Style.column
    ([ Input.popover After (renderGuardButton isguarded >-> Either.in1) <| (renderStep status cont match >-> Either.in3)]
    ++ guard ) 
        >-> fix3 isguarded (label ~ expr) (cont ~ match)
  where
  guard = case isguarded of
    true -> [renderOptionWithLabel status label expr >-> Either.in2, Style.line Dashed empty] --hacky extra line to ensure enough space
    false -> []
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
renderGroup :: Par -> (Checked Task -> Widget (Checked Task)) -> Array (Checked Task) -> Widget (Task (Checked Task))
renderGroup par trans tasks =
  Style.element
    [ void Attr.onClick ->> other par tasks
    , void Attr.onDoubleClick ->> this par (tasks ++ [ Builder.item ])
    ]
    [ Style.group (stroke par)
        [ Concur.traverse trans tasks >-> this par
        -- , Input.button Action Secondary Small "+" ->> this par (tasks ++ [ Builder.item ])
        ]
    ]

---- Editors ----

-- | [[ i |   w   ]]
renderEditor :: forall a. Widget a -> Widget a -> Widget a
renderEditor =
  Input.addon Medium

renderEnter :: Labeled BasicType -> Name -> Widget Name
renderEnter types name =
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

type IsGuarded = Bool


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
  switch true = false
  switch false = true

addLabels :: forall f v. Functor f => f v -> f (String * v)
addLabels = map ("" ~ _)

removeLabels :: forall f v k. Functor f => f (k * v) -> f v
removeLabels = map snd
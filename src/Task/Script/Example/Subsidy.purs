module Task.Script.Example.Subsidy where

import Preload hiding (pair)

import Data.HashMap as HashMap
import Task.Script.Annotation (Checked)
import Task.Script.Builder (branch, enter, execute, lift, pair, hole, cont, end, match, step, view)
import Task.Script.Context (Context, Typtext, recordOf', recordOf, taskOf, (:->))
import Task.Script.Syntax (Arguments(..), Constant(..), Expression(..), Match(..), Task)
import Task.Script.Type (BasicType(..), PrimType(..))
import Task.Script.World (World, Tasktext)

---- Context -------------------------------------------------------------------

types :: Typtext
types =
  from
    [ "Citizen"
        ~ BPrimitive (TBuiltin "Citizen")
    -- ~ recordOf'
    --     [ "ssn" ~ BName "Nat"
    --     , "name" ~ BName "String"
    --     , "address" ~ BName "Address"
    --     ]
    , "Company"
        ~ BPrimitive (TBuiltin "Company")
    -- ~ recordOf'
    --     [ "coc" ~ BName "Nat"
    --     , "name" ~ BName "String"
    --     , "address" ~ BName "Address"
    --     ]
    , "Address"
        ~ BPrimitive (TBuiltin "Address")
    -- ~ recordOf'
    --     [ "street" ~ BName "String"
    --     , "house number" ~ BName "Nat"
    --     , "postal code" ~ BName "Nat"
    --     , "city" ~ BName "String"
    --     ]
    , "Documents"
        ~ BPrimitive (TBuiltin "Documents")
    -- ~ recordOf'
    --     [ "invoice amount" ~ BName "Nat"
    --     , "invoice date" ~ BName "Date"
    --     , "roof photos" ~ BList (BName "String")
    --     ]
    , "Declaration"
        ~ BPrimitive (TBuiltin "Declaration")
    -- ~ recordOf'
    --     [ "roof photos" ~ BList (BName "String")
    --     , "date" ~ BName "Date"
    --     ]
    , "Dossier"
        ~ recordOf'
            [ "documents" ~ BName "Documents"
            , "declaration" ~ BName "Declaration"
            ]
    ]

context :: Context
context =
  from
    [ "check conditions"
        ~ recordOf [ "details" ~ BName "Citizen" ]
        :-> taskOf [ "approved" ~ BName "Bool" ]
    , "provide documents"
        ~ recordOf [ "details" ~ BName "Citizen" ]
        :-> taskOf [ "documents" ~ BName "Documents" ]
    , "select contractor"
        ~ recordOf []
        :-> taskOf [ "contractor" ~ BName "Company" ]
    , "provide declaration"
        ~ recordOf [ "contractor" ~ BName "Company", "details" ~ BName "Citizen" ]
        :-> taskOf [ "declaration" ~ BName "Declaration" ]
    , "submit request"
        -- ~ recordOf [ "dossier" ~ BName "Dossier" ]
        ~ recordOf
            [ "documents" ~ BName "Documents"
            , "declaration" ~ BName "Declaration"
            ]
        :-> taskOf []
    ]

---- Tasks ---------------------------------------------------------------------

tasks :: Tasktext
tasks =
  from
    [ "request subsidy" ~ (from [] ~ request_subsidy)
    , "request subsidy partial" ~ (from [] ~ request_subsidy_partial)
    ]

{-
  {value = details} <- enter Citizen "Passenger details"
  {approved} <- check_conditions {details}
  branch
    not approved |->
      view "Cannot apply for this subsidy" {}
    approved |->
      {documents, declaration} <- pair
        provide_documents {details}
        {contractor} <- select_contractor {}
        {declaration} <- provide_declaration {details, contractor}
        done {contractor, declaration}
    submit_request {dossier = {documents, declaration}}
-}

request_subsidy :: Checked Task
request_subsidy =
  cont (MRecord <| from [ "value" ~ MBind "details" ]) (enter "Citizen")
    <| branch (MRecord <| from [ "approved" ~ MBind "approved" ]) (execute "check conditions" (ARecord <| from [ "details" ~ Variable "details" ]))
      [ Variable "not" `Apply` Variable "approved"
          ~
            ( view (Constant (S "Cannot approve"))
            )
      , Variable "approved"
          ~
            ( step (MRecord <| from [ "documents" ~ MBind "documents", "declaration" ~ MBind "declaration" ])
                ( pair
                    [ step (MRecord <| from [ "documents" ~ MBind "documents" ]) (execute "provide documents" (ARecord <| from [ "details" ~ Variable "details" ]))
                        -- <| lift Wildcard -- XXX Something is wrong with Wildcard...
                        <| lift (Record <| from [ "documents" ~ Variable "documents" ])
                    , step (MRecord <| from [ "contractor" ~ MBind "contractor" ]) (execute "select contractor" (ARecord HashMap.empty))
                        <| step (MRecord <| from [ "declaration" ~ MBind "declaration" ]) (execute "provide declaration" (ARecord <| from [ "contractor" ~ Variable "contractor", "details" ~ Variable "details" ]))
                        <| lift (Record <| from [ "contractor" ~ Variable "contractor", "declaration" ~ Variable "declaration" ])
                    -- <| lift Wildcard
                    ]
                )
                -- <| execute "submit request" (ARecord <| from [ "dossier" ~ Record (from [ "declaration" ~ Variable "declaration", "documents" ~ Variable "documents" ]) ])
                <| execute "submit request" (ARecord <| from [ "declaration" ~ Variable "declaration", "documents" ~ Variable "documents" ])
            )
      ]

request_subsidy_partial :: Checked Task
request_subsidy_partial =
  cont (MRecord <| from [ "value" ~ MBind "details" ]) (enter "Citizen") --cont = step, branch = select
    <| branch (MRecord <| from [ "approved" ~ MBind "approved" ]) (execute "check conditions" (ARecord <| from [ "details" ~ Variable "details" ]))
      [ Variable "not" `Apply` Variable "approved"
          ~
            ( view (Constant (S "Cannot approve"))
            )
      , Variable "approved"
          ~
            ( step (MRecord <| from [ "documents" ~ MBind "documents", "declaration" ~ MBind "declaration" ])
                ( pair
                    [ step (MRecord <| from [ "documents" ~ MBind "documents" ]) (execute "provide documents" (ARecord <| from [ "details" ~ Variable "details" ]))
                        -- <| lift Wildcard -- XXX Something is wrong with Wildcard...
                        <| lift (Record <| from [ "documents" ~ Variable "documents" ])
                    -- , step (MRecord <| from [ "contractor" ~ MBind "contractor" ]) (execute "select contractor" (ARecord HashMap.empty)) <|
                    , end (match []) hole
                    ]
                )
                -- <| execute "submit request" (ARecord <| from [ "dossier" ~ Record (from [ "declaration" ~ Variable "declaration", "documents" ~ Variable "documents" ]) ])
                <| execute "submit request" (ARecord <| from [ "declaration" ~ Variable "declaration", "documents" ~ Variable "documents" ])
            )
      ]

---- World ---------------------------------------------------------------------

world :: World
world = { types, context, tasks }
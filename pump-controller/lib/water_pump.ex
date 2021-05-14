defmodule WaterPump do
  require Oracle
  @oracle spawn(Oracle, :start, [])

  @pumps [0, 1, 2, 3, 4]
  def pumps, do: @pumps

  @alternatio_n_pumps [0, 1, 2]
  def alternatio_n_pumps, do: @alternatio_n_pumps

  @thresholds %{
    "x0" => 1,
    "x1" => 10,
    "x2" => 20,
    "x3" => 30,
    "x4" => 40,
    "x5" => 50,
    "x6" => 60,
    "x7" => 70,
    "x8" => 80,
    "x9" => 90,
    "x10" => 100,
    "x11" => 110,
    "xn" => 120
  }
  def thresholds, do: @thresholds

  def defcon6_condition(variables) do
    variables[:new_level] < @thresholds["x1"]
  end

  def defcon5_condition(variables) do
    Enum.any?([
      Enum.all?([
        variables[:old_level] >= @thresholds["x2"],
        @thresholds["x2"] > variables[:new_level]
      ]),
      Enum.all?([
        variables[:old_level] < @thresholds["x1"],
        @thresholds["x1"] <= variables[:new_level]
      ])
    ])
  end

  def defcon4_condition(variables) do
    Enum.any?([
      Enum.all?([
        variables[:old_level] < @thresholds["x5"],
        @thresholds["x5"] <= variables[:new_level],
        variables[:requested_pumps] > 4
      ]),
      Enum.all?([
        variables[:old_level] >= @thresholds["x3"],
        @thresholds["x3"] > variables[:new_level]
      ])
    ])
  end

  def defcon_plus1_condition(variables) do
    Enum.any?([
      Enum.all?([
        variables[:old_level] >= @thresholds["x7"],
        @thresholds["x7"] > variables[:new_level],
        variables[:requested_pumps] < 1
      ]),
      Enum.all?([
        variables[:old_level] >= @thresholds["x6"],
        @thresholds["x6"] > variables[:new_level],
        variables[:requested_pumps] < 2
      ]),
      Enum.all?([
        variables[:old_level] >= @thresholds["x4"],
        @thresholds["x4"] > variables[:new_level],
        variables[:requested_pumps] < 3
      ])
    ])
  end

  def defcon_minus1_condition(variables) do
    Enum.any?([
      Enum.all?([
        variables[:old_level] < @thresholds["x11"],
        @thresholds["x11"] <= variables[:new_level]
      ]),
      Enum.all?([
        variables[:old_level] < @thresholds["x10"],
        @thresholds["x10"] <= variables[:new_level],
        variables[:requested_pumps] > 1
      ]),
      Enum.all?([
        variables[:old_level] < @thresholds["x9"],
        @thresholds["x9"] <= variables[:new_level],
        variables[:requested_pumps] > 2
      ]),
      Enum.all?([
        variables[:old_level] < @thresholds["x8"],
        @thresholds["x8"] <= variables[:new_level],
        variables[:requested_pumps] > 3
      ])
    ])
  end

  def defcon0_condition(variables) do
    variables[:new_level] > @thresholds["xn"]
  end

  def defcon(variables) do
    cond do
      defcon6_condition(variables) -> 6
      defcon5_condition(variables) -> 5
      defcon0_condition(variables) -> 0
      defcon_plus1_condition(variables) -> variables[:requested_pumps] + 1
      defcon_minus1_condition(variables) -> variables[:requested_pumps] - 1
      true -> variables[:requested_pumps]
    end
  end

  def activate_condition(variables, p) do
    Enum.all?([
      variables[:states][p] == "OFF",
      if(Enum.member?(@alternatio_n_pumps, p),
        do: variables[:onp] == p,
        else:
          if(p == 3,
            do:
              Enum.all?(@alternatio_n_pumps, fn i -> variables[:requested_states][i] != "OFF" end),
            else: Enum.all?(0..3, fn i -> variables[:requested_states][i] != "OFF" end)
          )
      )
    ])
  end

  def activate(variables, p) do
    Map.merge(
      %{
        requested_states: Map.put(variables[:requested_states], p, "ON"),
        ofp: variables[:ofp]
      },
      if(Enum.member?(@alternatio_n_pumps, p),
        do: %{
          onp: rem(p + 1, 3)
        },
        else:
          if(p == 3,
            do: %{},
            else: %{
              onp: variables[:onp]
            }
          )
      )
    )
  end

  def deactivate_condition(variables, p) do
    Enum.all?([
      variables[:states][p] == "ON",
      if(Enum.member?(@alternatio_n_pumps, p),
        do:
          Enum.all?([
            Enum.all?(3..4, fn i -> variables[:requested_states][i] != "ON" end),
            variables[:ofp] == p
          ]),
        else: false
      )
    ])
  end

  def deactivate(variables, p) do
    Map.merge(
      %{
        requested_states: Map.put(variables[:requested_states], p, "OFF"),
        onp: variables[:onp]
      },
      if(Enum.member?(@alternatio_n_pumps, p),
        do: %{
          ofp: rem(p + 1, 3)
        },
        else: %{
          ofp: variables[:ofp]
        }
      )
    )
  end

  def select_pumps_condition(variables, pumpCount) do
    Enum.all?([
      Enum.all?(@pumps, fn p ->
        not Enum.member?(MapSet.new(["STARTING", "STOPPING"]), variables[:states][p])
      end),
      if(Enum.count(Enum.filter(@pumps, fn p -> variables[:states][p] == "ON" end)) < pumpCount,
        do: Enum.any?(@pumps, fn p -> activate_condition(variables, p) end),
        else:
          if(
            Enum.count(Enum.filter(@pumps, fn p -> variables[:states][p] == "ON" end)) >
              pumpCount,
            do: Enum.any?(@pumps, fn p -> deactivate_condition(variables, p) end),
            else: false
          )
      )
    ])
  end

  def select_pumps(variables, pumpCount) do
    Map.merge(
      %{
        requested_pumps: pumpCount
      },
      if(Enum.count(Enum.filter(@pumps, fn p -> variables[:states][p] == "ON" end)) < pumpCount,
        do:
          decide_action(
            List.flatten([
              Enum.map(@pumps, fn p ->
                [
                  %{
                    action: "activate(#{inspect(p)})",
                    condition: activate_condition(variables, p),
                    state: activate(variables, p)
                  }
                ]
              end)
            ])
          ),
        else:
          if(
            Enum.count(Enum.filter(@pumps, fn p -> variables[:states][p] == "ON" end)) >
              pumpCount,
            do:
              decide_action(
                List.flatten([
                  Enum.map(@pumps, fn p ->
                    [
                      %{
                        action: "deactivate(#{inspect(p)})",
                        condition: deactivate_condition(variables, p),
                        state: deactivate(variables, p)
                      }
                    ]
                  end)
                ])
              ),
            else: %{
              states: variables[:states],
              requested_states: variables[:requested_states],
              ofp: variables[:ofp],
              onp: variables[:onp]
            }
          )
      )
    )
  end

  def success_on_condition(variables, p) do
    variables[:states][p] == "STARTING"
  end

  def success_on(variables, p) do
    %{
      states: Map.put(variables[:states], p, "ON"),
      requested_states: variables[:requested_states]
    }
  end

  def failure_on_condition(variables, p) do
    variables[:states][p] == "STARTING"
  end

  def failure_on(variables, p) do
    %{
      states: Map.put(variables[:states], p, "DAMAGED"),
      requested_states: Map.put(variables[:requested_states], p, "OFF")
    }
  end

  def success_off_condition(variables, p) do
    variables[:states][p] == "STOPPING"
  end

  def success_off(variables, p) do
    %{
      states: Map.put(variables[:states], p, "OFF"),
      requested_states: variables[:requested_states]
    }
  end

  def failure_off_condition(variables, p) do
    variables[:states][p] == "STOPPING"
  end

  def failure_off(variables, p) do
    %{
      states: Map.put(variables[:states], p, "DAMAGED"),
      requested_states: Map.put(variables[:requested_states], p, "ON")
    }
  end

  def switch_on_condition(variables, p) do
    Enum.all?([variables[:states][p] == "OFF", variables[:requested_states][p] == "ON"])
  end

  def switch_on(variables, p) do
    %{
      states: Map.put(variables[:states], p, "STARTING")
    }
  end

  def switch_off_condition(variables, p) do
    Enum.all?([variables[:states][p] == "ON", variables[:requested_states][p] == "OFF"])
  end

  def switch_off(variables, p) do
    %{
      states: Map.put(variables[:states], p, "STOPPING")
    }
  end

  def switch_pumps_condition(variables) do
    Enum.any?(@pumps, fn p ->
      Enum.any?([switch_on_condition(variables, p), switch_off_condition(variables, p)])
    end)
  end

  def switch_pumps(variables) do
    decide_action(
      List.flatten([
        Enum.map(@pumps, fn p ->
          [
            %{
              action: "switchON(#{inspect(p)})",
              condition: switch_on_condition(variables, p),
              state: switch_on(variables, p)
            },
            %{
              action: "switchOFF(#{inspect(p)})",
              condition: switch_off_condition(variables, p),
              state: switch_off(variables, p)
            }
          ]
        end)
      ])
    )
  end

  def water_level_up_condition(variables) do
    true
  end

  def water_level_up(variables) do
    %{
      new_level: variables[:new_level] + 10
    }
  end

  def water_level_down_condition(variables) do
    true
  end

  def water_level_down(variables) do
    %{
      new_level: variables[:new_level] - 10
    }
  end

  def pump_selection_condition(variables) do
    select_pumps_condition(variables, defcon(variables))
  end

  def pump_selection(variables) do
    Map.merge(
      %{
        new_level: variables[:new_level],
        states: variables[:states]
      },
      select_pumps(variables, defcon(variables))
    )
  end

  def pump_switching_condition(variables) do
    switch_pumps_condition(variables)
  end

  def pump_switching(variables) do
    Map.merge(
      %{
        new_level: variables[:new_level],
        requested_pumps: variables[:requested_pumps],
        onp: variables[:onp],
        ofp: variables[:ofp],
        requested_states: variables[:requested_states]
      },
      switch_pumps(variables)
    )
  end

  def pump_status_change_condition(variables) do
    Enum.any?(@pumps, fn p ->
      Enum.any?([
        success_on_condition(variables, p),
        success_off_condition(variables, p),
        failure_on_condition(variables, p),
        failure_off_condition(variables, p)
      ])
    end)
  end

  def pump_status_change(variables) do
    Map.merge(
      %{
        new_level: variables[:new_level],
        requested_pumps: variables[:requested_pumps],
        onp: variables[:onp],
        ofp: variables[:ofp]
      },
      decide_action(
        List.flatten([
          Enum.map(@pumps, fn p ->
            [
              %{
                action:
                  "ActionOr [ActionCall \"successON\" [Arith \(Ref \"p\"\)\],ActionCall \"successOFF\" [Arith \(Ref \"p\"\)\],ActionCall \"failureON\" [Arith \(Ref \"p\"\)\],ActionCall \"failureOFF\" [Arith \(Ref \"p\"\)\]\]",
                condition:
                  Enum.any?([
                    success_on_condition(variables, p),
                    success_off_condition(variables, p),
                    failure_on_condition(variables, p),
                    failure_off_condition(variables, p)
                  ]),
                state:
                  decide_action(
                    List.flatten([
                      %{
                        action: "successON(#{inspect(p)})",
                        condition: success_on_condition(variables, p),
                        state: success_on(variables, p)
                      },
                      %{
                        action: "successOFF(#{inspect(p)})",
                        condition: success_off_condition(variables, p),
                        state: success_off(variables, p)
                      },
                      %{
                        action: "failureON(#{inspect(p)})",
                        condition: failure_on_condition(variables, p),
                        state: failure_on(variables, p)
                      },
                      %{
                        action: "failureOFF(#{inspect(p)})",
                        condition: failure_off_condition(variables, p),
                        state: failure_off(variables, p)
                      }
                    ])
                  )
              }
            ]
          end)
        ])
      )
    )
  end

  def water_level_change_condition(variables) do
    Enum.any?([water_level_up_condition(variables), water_level_down_condition(variables)])
  end

  def water_level_change(variables) do
    Map.merge(
      %{
        states: variables[:states],
        requested_states: variables[:requested_states],
        requested_pumps: variables[:requested_pumps],
        onp: variables[:onp],
        ofp: variables[:ofp]
      },
      decide_action(
        List.flatten([
          %{
            action: "waterLevelUp()",
            condition: water_level_up_condition(variables),
            state: water_level_up(variables)
          },
          %{
            action: "waterLevelDown()",
            condition: water_level_down_condition(variables),
            state: water_level_down(variables)
          }
        ])
      )
    )
  end

  #  Spec == WPInit /\[][WPNext]_<< states, requestedStates, requestedPumps, onp, ofp, newLevel, oldLevel >>
  def main(variables) do
    IO.puts(inspect(variables))

    main(
      Map.merge(
        %{
          old_level: variables[:new_level]
        },
        decide_action(
          List.flatten([
            %{
              action: "algorithmStep()",
              condition:
                if(
                  Enum.count(Enum.filter(@pumps, fn p -> variables[:states][p] == "ON" end)) !=
                    variables[:requested_pumps],
                  do: pump_switching_condition(variables),
                  else: pump_selection_condition(variables)
                ),
              state:
                if(
                  Enum.count(Enum.filter(@pumps, fn p -> variables[:states][p] == "ON" end)) !=
                    variables[:requested_pumps],
                  do: pump_switching(variables),
                  else: pump_selection(variables)
                )
            },
            %{
              action: "pumpStatusChange()",
              condition: pump_status_change_condition(variables),
              state: pump_status_change(variables)
            },
            %{
              action: "waterLevelChange()",
              condition: water_level_change_condition(variables),
              state: water_level_change(variables)
            }
          ])
        )
      )
    )
  end

  def decide_action(actions) do
    possible_actions = Enum.filter(actions, fn action -> action[:condition] end)
    different_states = Enum.uniq_by(possible_actions, fn action -> action[:state] end)

    cond do
      Enum.count(different_states) == 1 ->
        Enum.at(possible_actions, 0)[:state]

      Enum.empty?(different_states) ->
        %{}

      true ->
        actions_names = Enum.map(possible_actions, fn action -> action[:action] end)
        send(@oracle, {self(), actions_names})

        n =
          receive do
            {:ok, n} -> n
          end

        Enum.at(possible_actions, n)[:state]
    end
  end
end

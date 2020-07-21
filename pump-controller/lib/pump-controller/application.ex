defmodule PumpController.Application do
  # See https://hexdocs.pm/elixir/Application.html
  # for more information on OTP Applications
  @moduledoc false

  use Application

  require Tortoise
  require Logger
  require WaterPump

  def start(_type, _args) do
    import Supervisor.Spec, warn: false
    children = [
      {Tortoise.Supervisor,
      [
        name: MyApp.Connection.Supervisor,
        strategy: :one_for_one
      ]}
    ]

    {:ok, pid} =
      Supervisor.start_link(children, strategy: :one_for_one, name: PumpControllerManager.Supervisor)

    supervisor = Tortoise.Supervisor.start_child(
      MyApp.Connection.Supervisor,
      client_id: "aaa",
      handler: {SensorsHandler, []},
      user_name: "pumps",
      password: "pumps",
      server: {Tortoise.Transport.Tcp, host: "localhost", port: 8883},
      subscriptions: [{"water_level", 0}, {"pumps/+/state", 0}]
    )

    Logger.info(inspect supervisor)

    WaterPump.main(%{
          states: WaterPump.pumps() |> Enum.map(fn p -> {p, "OFF"} end) |> Enum.into(%{}),
          requested_states: WaterPump.pumps() |> Enum.map(fn p -> {p, "OFF"} end) |> Enum.into(%{}),
          onp: 0,
          ofp: 0,
          requested_pumps: 0,
          new_level: 120,
          old_level: 120
    })

    {:ok, pid}
  end
end

defmodule Mqtt.Application do
  # See https://hexdocs.pm/elixir/Application.html
  # for more information on OTP Applications
  @moduledoc false

  use Application

  require Tortoise
  require Logger

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
      Supervisor.start_link(children, strategy: :one_for_one, name: MqttManager.Supervisor)

    a = Tortoise.Supervisor.start_child(
      MyApp.Connection.Supervisor,
      client_id: "aaa",
      handler: {Tortoise.Handler.Logger, []} ,
      user_name: "pumps",
      password: "pumps",
      server: {Tortoise.Transport.Tcp, host: "localhost", port: 8883},
      subscriptions: [{"test", 0}]
    )

    Logger.info(inspect a)
    b = Tortoise.Connection.subscribe(WaterPump, "test", qos: 0)
    Logger.info(inspect b)

    listen
    {:ok, pid}
  end

  def listen do
    receive do
      {p, as} -> Logger.debug(inspect p)
    end

    listen()
  end
end

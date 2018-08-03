-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 4

-- check that all functions are total
%default total

||| Powersources for vehicles
data PowerSource = Petrol | Pedal | Electric

||| Vehicles
data Vehicle : PowerSource -> Type where
  Unicycle : Vehicle Pedal
  Bicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Tram : Vehicle Electric
  ElectricCar : Vehicle Electric

wheels : Vehicle power -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels Motorcycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Tram = 10
wheels ElectricCar = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motorcycle fuel) = Motorcycle 50
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel Unicycle impossible
refuel Bicycle impossible
refuel Tram impossible
refuel ElectricCar impossible

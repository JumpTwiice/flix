///
/// Prints the weather condition an temperature based on the user's location.
///
def main(): Unit \ Net + IO = 
    run {
        match Location.Location.getLocation() {
            case Err(err) => Logger.fatal(err)
            case Ok(loc) => match Weather.getWeather(loc) {
                case Err(err) => Logger.fatal(err)
                case Ok(weather) => Display.Display.display(loc, weather)
            }
        }
    } with Weather.weatherWithHttpAndFile
    with Location.locationWithHttp
    with Display.displayWithIO
    with HttpWithResult.runWithIO
    with Logger.runWithIO
    with FileReadWithResult.runWithIO

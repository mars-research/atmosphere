use uart_16550::SerialPort;

const SERIAL_IO_PORT: u16 = 0x3F8;

pub fn init() {
    let mut port = unsafe { SerialPort::new(SERIAL_IO_PORT) };
    port.init();
}

pub fn get_writer() -> SerialPort {
    unsafe { SerialPort::new(SERIAL_IO_PORT) }
}

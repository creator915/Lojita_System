"""Linux side of the PTY and connected stream differential trace."""
import os
import select
import socket
import termios
import tty

trace = []

def read(fd, count):
    try:
        data = os.read(fd, count)
    except OSError as error:
        trace.append(-error.errno)
        return
    encoded = 0
    for byte in data:
        encoded = encoded * 257 + byte + 1
    trace.append(encoded)

def write(fd, data):
    try:
        trace.append(os.write(fd, data))
    except OSError as error:
        trace.append(-error.errno)

def ready(fd, events, timeout=0):
    poller = select.poll()
    poller.register(fd, events)
    return next((mask for _, mask in poller.poll(timeout)), 0)

def pair(raw):
    master, slave = os.openpty()
    os.set_blocking(master, False)
    os.set_blocking(slave, False)
    if raw:
        tty.setraw(slave)
    else:
        attrs = termios.tcgetattr(slave)
        attrs[0] |= termios.ICRNL
        attrs[3] |= termios.ICANON
        attrs[6][termios.VEOF] = b'\x04'
        termios.tcsetattr(slave, termios.TCSANOW, attrs)
    return master, slave

def slave_hangup():
    master, slave = pair(True)
    alias = os.dup(master)
    os.close(master)
    write(alias, b'abc')
    assert ready(slave, select.POLLIN, 2000)
    read(slave, 1)
    trace.append(ready(slave, 5))
    os.dup2(slave, alias)
    trace.append(ready(slave, 5))
    read(slave, 2)
    read(alias, 2)
    write(slave, b'')
    write(slave, b'x')
    os.close(alias)
    os.close(slave)

def master_hangup():
    master, slave = pair(True)
    alias = os.dup(slave)
    os.close(slave)
    read(master, 1)
    write(alias, b'abc')
    assert ready(master, select.POLLIN, 2000)
    os.close(alias)
    trace.append(ready(master, 5))
    read(master, 1)
    read(master, 4)
    trace.append(ready(master, 5))
    read(master, 4)
    read(master, 4)
    write(master, b'x')
    os.close(master)

def canonical_record():
    master, slave = pair(False)
    write(master, b'abc\r12\n\x04z\n')
    assert ready(slave, select.POLLIN, 2000)
    read(slave, 1)
    read(slave, 32)
    read(slave, 32)
    trace.append(ready(slave, 1))
    read(slave, 3)
    trace.append(ready(slave, 1))
    read(slave, 1)
    read(slave, 3)
    trace.append(ready(slave, 1))
    read(slave, 3)
    os.close(master)
    os.close(slave)

def peer_fin():
    with socket.socket() as listener, socket.socket() as client:
        listener.bind(('127.0.0.1', 0))
        listener.listen()
        client.connect(listener.getsockname())
        peer, _ = listener.accept()
        with peer:
            peer.sendall(b'a\0b')
            peer.shutdown(socket.SHUT_WR)
            client.setblocking(False)
            fd = client.fileno()
            assert ready(fd, select.POLLIN, 2000)
            read(fd, 2)
            read(fd, 2)
            assert ready(fd, select.POLLIN, 2000)
            trace.append(ready(fd, 5))
            read(fd, 1)
            read(fd, 1)

slave_hangup()
master_hangup()
canonical_record()
peer_fin()
print(','.join(map(str, trace)))

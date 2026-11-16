# g53_relay.py — node1 side: public listener :18123 paired with pooled
# reverse tunnels from 115 (each tunnel connection announces "TUN\n").
# Usage: python3 g53_relay.py
import socket, threading, select, sys

PUB = ('0.0.0.0', 18123)   # Kai-facing
TUN = ('0.0.0.0', 18124)   # 115 tunnel pool
tun_pool = []
pool_lock = threading.Lock()

def pump(a, b):
    try:
        socks = [a, b]
        while True:
            r, _, _ = select.select(socks, [], [], 300)
            if not r:
                break
            for s in r:
                data = s.recv(65536)
                if not data:
                    return
                (b if s is a else a).sendall(data)
    except Exception:
        pass
    finally:
        for s in (a, b):
            try: s.close()
            except Exception: pass

def tun_server():
    srv = socket.socket(); srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind(TUN); srv.listen(16)
    while True:
        c, _ = srv.accept()
        try:
            c.settimeout(10)
            head = c.recv(4)
            if head == b'TUN\n':
                c.settimeout(None)
                with pool_lock:
                    tun_pool.append(c)
            else:
                c.close()
        except Exception:
            try: c.close()
            except Exception: pass

def pub_server():
    srv = socket.socket(); srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind(PUB); srv.listen(8)
    while True:
        c, _ = srv.accept()
        t = None
        with pool_lock:
            while tun_pool:
                t = tun_pool.pop(0)
                try:
                    t.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
                    # probe: closed pooled conns raise on zero-length send
                    t.settimeout(3)
                    t.send(b'')
                    t.settimeout(None)
                    break
                except Exception:
                    t = None
        if t is None:
            c.close(); continue
        threading.Thread(target=pump, args=(c, t), daemon=True).start()

threading.Thread(target=tun_server, daemon=True).start()
print('g53_relay: pub %s tun %s' % (PUB, TUN), flush=True)
pub_server()

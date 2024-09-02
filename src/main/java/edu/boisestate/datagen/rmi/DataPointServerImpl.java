package edu.boisestate.datagen.rmi;

import java.rmi.AlreadyBoundException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.server.UnicastRemoteObject;
import edu.boisestate.datagen.reporting.InstrumentationRecord;
import edu.boisestate.datagen.server.NewCache;

public class DataPointServerImpl extends UnicastRemoteObject implements DataPointServer {
    public DataPointServerImpl() throws RemoteException {
        super();
    }

    public void start() throws AlreadyBoundException {
        System.out.println("Starting DataPointServer");
        try {
            DataPointServerImpl server = new DataPointServerImpl();
            LocateRegistry.createRegistry(1099);
            LocateRegistry.getRegistry().bind("DataPointServer", server);
            System.out.println("DataPointServer bound");
        } catch (RemoteException e) {
            System.err.println("Failed to bind DataPointServer");
            e.printStackTrace();
        }
    }

    @Override
    public void receiveDataPoint(InstrumentationRecord record) throws RemoteException, NotBoundException {
        NewCache.getInstance().add_instrumentation_data(record);
    }
}

package edu.boisestate.datagen.rmi;

import java.rmi.AlreadyBoundException;
import java.rmi.NotBoundException;
import java.util.Random;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.server.ExportException;
import java.rmi.server.UnicastRemoteObject;
import edu.boisestate.datagen.reporting.InstrumentationRecord;
import edu.boisestate.datagen.reporting.Cache;

public class DataPointServerImpl extends UnicastRemoteObject implements DataPointServer {
    public static int datagenport;

    public DataPointServerImpl() throws RemoteException {
        super();
    }

    public static int getDatagenport() {
        return datagenport;
    }

    public void start() throws AlreadyBoundException {
        DataPointServerImpl.datagenport = (new Random()).ints(10000, 20000).findFirst().getAsInt();
        String identifier = String.format("DataPointServer_%d", DataPointServerImpl.getDatagenport());
        System.out.println("Starting DataPointServer on port " + DataPointServerImpl.getDatagenport());

        try {
            LocateRegistry.createRegistry(1099);
        } catch (RemoteException e) {
            System.err.println("Failed to create registry because of RemoteException " + e.getMessage());
        }

        try {
            DataPointServerImpl server = new DataPointServerImpl();
            LocateRegistry.getRegistry().bind(identifier, server);

            System.out.println("DataPointServer bound on port " + DataPointServerImpl.getDatagenport() + " as "
                    + identifier);
        } catch (RemoteException e) {
            System.err.println("Failed to bind DataPointServer because of RemoteException " + e.getMessage());
            if (e instanceof ExportException) {
                // Port was already in use.
                // Assign a different port, and try again.

                System.err.println("Port " + datagenport + " already in use. Retrying...");
                start();
            }
        }
    }

    @Override
    public void receiveDataPoint(InstrumentationRecord record) throws RemoteException, NotBoundException {
        Cache.getInstance().add_instrumentation_data(record);
    }
}

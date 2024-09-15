package edu.boisestate.datagen.rmi;

import java.rmi.AlreadyBoundException;
import java.rmi.NotBoundException;
import java.util.Random;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.rmi.server.ExportException;
import java.rmi.server.UnicastRemoteObject;
import edu.boisestate.datagen.reporting.InstrumentationRecord;
import edu.boisestate.datagen.reporting.Cache;

public class DataPointServerImpl extends UnicastRemoteObject implements DataPointServer {
    public static int datagenport;

    public DataPointServerImpl() throws RemoteException {
        super();
    }

    public static int getDatagenInstanceId() {
        return datagenport;
    }

    public void start() throws AlreadyBoundException {
        DataPointServerImpl.datagenport = (new Random()).ints(10000, 20000).findFirst().getAsInt();
        String identifier = String.format("DataPointServer_%d", DataPointServerImpl.getDatagenInstanceId());
        System.out.println("Starting DataPointServer on port " + DataPointServerImpl.getDatagenInstanceId());

        Registry registry = null;
        try {
            registry = LocateRegistry.createRegistry(1099);
        } catch (RemoteException e) {
            try {
                registry = LocateRegistry.getRegistry(1099);
            } catch (RemoteException e1) {
                System.out.println("Failed to create registry on port 1099, and to get it also. Exiting...");
                // TODO Auto-generated catch block
                e1.printStackTrace();
                System.exit(1);
            }
        }

        try {
            DataPointServerImpl server = new DataPointServerImpl();
            registry.bind(identifier, server);

            System.out.println("DataPointServer bound on port " + DataPointServerImpl.getDatagenInstanceId() + " as "
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

import "../globals.css";

export const metadata = { title: "The Lumenary" };

export default function RootRedirectLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
